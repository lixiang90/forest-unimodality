import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell175.Parameters
import ForestUnimodality.BinomialMassData.Q57_107.Batch000_049
import ForestUnimodality.BinomialMassData.Q57_107.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree000.table
  base := (4025015626651457216865992421/100000000000000000000000000)
  polynomial :=
    { denominator := 133750000000000000000000000000000000000000
      center := (627)
      previous := (0)
      next := (550)
      square := (23250507636885469377185930350000000000000)
      linear := (-93292429216789535956211310225000000000000)
      constant := (5383458400646324027558264863087500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree000.table
  base := (4025015626651457216865992421/100000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (319)
      previous := (0)
      next := (275)
      square := (11733901050390797629607852700000000000000)
      linear := (-47082160539314345248929072450000000000000)
      constant := (2716885547989733621384544884175000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree001.table
  base := (119354987459879700065395526169757930230577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-50531391187205695425255225015900000000000000)
      constant := (1390589884142384752209588514398658543209876073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree001.table
  base := (237390149532812496393745751529547013109129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-6446005860091281811918850737800000000000000)
      constant := (176153673608973825629052620701239772556555041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12465659275774314887/25000000000000000000)
  directionHi := (49862637103097259549/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree002.table
  base := (74107117904094327517159102125223044920031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-61133622669625469461252009255500000000000000)
      constant := (902289576018008191991422743893478641289434919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree002.table
  base := (458654161899053087650444157131992631469/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-1951784595484153584238340412750000000000000)
      constant := (28479582665866175817566927979087810267272080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12465659275774314887/25000000000000000000)
  centralHi := (49862637103097259549/100000000000000000000)
  directionLo := (35258208823444019841/50000000000000000000)
  directionHi := (70516417646888039683/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree003.table
  base := (96661942535179248334520907705008866880913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-143471708304090486994497586990200000000000000)
      constant := (1285137882604128234701488162598846516919572937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree003.table
  base := (47721139716549704073148557941313557093659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-509348383543441492332659586900000000000000)
      constant := (4503284513057206567451721710646398124586379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/50000000000000000000)
  centralHi := (70516417646888039683/100000000000000000000)
  directionLo := (21591155215483368161/25000000000000000000)
  directionHi := (17272924172386694529/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree004.table
  base := (33016450512569307683375482936286103634557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-82338085634465017533245577734700000000000000)
      constant := (508271379008822891864773923859539600512043093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree004.table
  base := (4067653770300577331584186517387034628209/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-2632350856406819846755595869350000000000000)
      constant := (16054000858569850457633700623200592975857444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/25000000000000000000)
  centralHi := (17272924172386694529/20000000000000000000)
  directionLo := (99725274206194519097/100000000000000000000)
  directionHi := (49862637103097259549/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree005.table
  base := (46841841730129409641267065818331622179959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-185880634233769583138484723948600000000000000)
      constant := (890196927222234351105976251357078742338350591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree005.table
  base := (46113349353230669573853474657287529257571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-11890535947472611912056894390600000000000000)
      constant := (56407690441738411580880654888162608828769259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/100000000000000000000)
  centralHi := (49862637103097259549/50000000000000000000)
  directionLo := (111496246099928661853/100000000000000000000)
  directionHi := (55748123049964330927/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree006.table
  base := (17036260311196551194152058327483144198183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-103542548599304565605239146213900000000000000)
      constant := (424334706172043270472866423971954517924997167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree006.table
  base := (16752982397788749146853751870841745124561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-736203803850996913171744739100000000000000)
      constant := (2998225254527533489522612570438181355089441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/100000000000000000000)
  centralHi := (55748123049964330927/50000000000000000000)
  directionLo := (12213801813215665899/10000000000000000000)
  directionHi := (122138018132156658991/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree007.table
  base := (1001714849808474260917105489354510563123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-228289560163448679282471860907000000000000000)
      constant := (861253234520239836463402762809094785929880675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree007.table
  base := (24589214335376324735926240461551654404363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-14612800991163276962125916217000000000000000)
      constant := (54949869554841867848685432782071156060780627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/10000000000000000000)
  centralHi := (122138018132156658991/100000000000000000000)
  directionLo := (26384827497731494757/20000000000000000000)
  directionHi := (65962068744328736893/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree008.table
  base := (18297422016945857878704438822811814216983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-249494023128288227354465429386200000000000000)
      constant := (911284699612500005267492418157572460970238367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree008.table
  base := (17922170099658322864342841209210854274003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-15973933513008609487160427130200000000000000)
      constant := (58302698942382932512350245440714712765748187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26384827497731494757/20000000000000000000)
  centralHi := (65962068744328736893/50000000000000000000)
  directionLo := (35258208823444019841/25000000000000000000)
  directionHi := (28206567058755215873/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree009.table
  base := (2605745972109457548053959439969495306737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-270698486093127775426458997865400000000000000)
      constant := (989519391831746570885791086372053758834159565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree009.table
  base := (3177332503778560863930034966402486909423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (319)
      previous := (0)
      next := (275)
      square := (11733901050390797629607852700000000000000)
      linear := (-160509870693092055668471648550000000000000)
      constant := (587468719747003278876496019842867146554421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/25000000000000000000)
  centralHi := (28206567058755215873/20000000000000000000)
  directionLo := (29917582261858355729/20000000000000000000)
  directionHi := (74793955654645889323/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree010.table
  base := (8774651740269165532683485746895412861551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-291902949057967323498452566344600000000000000)
      constant := (1090666235561712352715808112902205581851897399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree010.table
  base := (4248444152317852469930926585800172223207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-9348099278349637268614724478300000000000000)
      constant := (35025406757105061251473158196548325550717903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29917582261858355729/20000000000000000000)
  centralHi := (74793955654645889323/50000000000000000000)
  directionLo := (39419875847051854551/25000000000000000000)
  directionHi := (31535900677641483641/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree011.table
  base := (262973858793088516655548706293573032953/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-78276853005701717892611533705950000000000000)
      constant := (302892155378504573978002739976825588271394485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree011.table
  base := (2507238391374359334130396593884893349947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-10028665539272303531131979934900000000000000)
      constant := (38959087939886849970221372091542087252111363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39419875847051854551/25000000000000000000)
  centralHi := (31535900677641483641/20000000000000000000)
  directionLo := (82687829164313665251/50000000000000000000)
  directionHi := (165375658328627330503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree012.table
  base := (1155079429679615276151589027401150686327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-167155937493823209821219851651500000000000000)
      constant := (675122665529881568324543430721515774207757823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree012.table
  base := (2092285895921173560773742822637274596823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-2379829288932215509699830087000000000000000)
      constant := (9658324184982464161525160917033619242342663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82687829164313665251/50000000000000000000)
  centralHi := (165375658328627330503/100000000000000000000)
  directionLo := (21591155215483368161/12500000000000000000)
  directionHi := (172729241723866945289/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree013.table
  base := (-37638280542114494723918226743096754033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-355516337952485967714433271782200000000000000)
      constant := (1505381009271884588344277261956291426315380915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree013.table
  base := (-191343784896340203026956615440295845797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-11389798061117636056166490848100000000000000)
      constant := (48494329763224551637849507022444024328413987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/12500000000000000000)
  centralHi := (172729241723866945289/100000000000000000000)
  directionLo := (179782294805070360357/100000000000000000000)
  directionHi := (89891147402535180179/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree014.table
  base := (-2316223153747968330111094926217509953599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-376720800917325515786426840261400000000000000)
      constant := (1676052299527992277573722046187735728541245049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree014.table
  base := (-622506752064300302860783832761552278563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-6035182161020151159341873152350000000000000)
      constant := (27012846292616840109877090364166828388927573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/100000000000000000000)
  centralHi := (89891147402535180179/50000000000000000000)
  directionLo := (93284452220416131557/50000000000000000000)
  directionHi := (37313780888166452623/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree015.table
  base := (-2066716186642752738689759697947455702573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-198962631941082531929210204370300000000000000)
      constant := (930789016179209028508248845892699579661241723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree015.table
  base := (-4288634375512453730637430691336855397679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-2833540129547326351378000391400000000000000)
      constant := (13341128341215971294566885970001714712788001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93284452220416131557/50000000000000000000)
  centralHi := (37313780888166452623/20000000000000000000)
  directionLo := (48279290774569931031/25000000000000000000)
  directionHi := (1544937304786237793/800000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree016.table
  base := (-5685505016583384254223909012632667991547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-419129726847004611930413977219800000000000000)
      constant := (2061435149261387892993693938613568584164778397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree016.table
  base := (-5823861542275436343993314489651812061009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-26862993687771269687436514435800000000000000)
      constant := (133011907714125555091199951300243829007524439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48279290774569931031/25000000000000000000)
  centralHi := (1544937304786237793/800000000000000000)
  directionLo := (99725274206194519097/50000000000000000000)
  directionHi := (39890109682477807639/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree017.table
  base := (-3504293400474186554416548479673836473179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-220167094905922080001203772849500000000000000)
      constant := (1137604908959728296770998417780514246218573629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree017.table
  base := (-3565828088597787264183801586880020473767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-14112063104808301106235512674500000000000000)
      constant := (73425218624783684793586837488464465074623857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/50000000000000000000)
  centralHi := (39890109682477807639/20000000000000000000)
  directionLo := (41117783909582439923/20000000000000000000)
  directionHi := (3212326867936128119/1562500000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree018.table
  base := (-8131881538223106486365954420701085079487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-461538652776683708074401114178200000000000000)
      constant := (2502567683890837836898782466434593276924953337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree018.table
  base := (-1648218174259246428586124803375979676191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1100)
      square := (46935604201563190518431410800000000000000)
      linear := (-1095750323387479064352056898600000000000000)
      constant := (5983872213274561217988443562144242743714215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41117783909582439923/20000000000000000000)
  centralHi := (3212326867936128119/1562500000000000000)
  directionLo := (105774626470332059523/50000000000000000000)
  directionHi := (211549252940664119047/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree019.table
  base := (-1815863876542455036332389693422575531341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-482743115741523256146394682657400000000000000)
      constant := (2743234770838897218153933772745024663708384455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree019.table
  base := (-2293998653992086956482596082637647451763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-7736597813326816815635011793850000000000000)
      constant := (44284218476484727679865014393257155007664773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/50000000000000000000)
  centralHi := (211549252940664119047/100000000000000000000)
  directionLo := (217346196190842635799/100000000000000000000)
  directionHi := (1086730980954213179/500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree020.table
  base := (-9870690494838566537824236009539760406181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-503947578706362804218388251136600000000000000)
      constant := (2996984501216955389916262711018779283109633731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree020.table
  base := (-1991213640342409091071795931493513448949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-32307523775152599787574558088600000000000000)
      constant := (193553047815870052781433681511706143478580895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/100000000000000000000)
  centralHi := (1086730980954213179/500000000000000000)
  directionLo := (111496246099928661853/50000000000000000000)
  directionHi := (222992492199857323707/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree021.table
  base := (-10522458049951862440398621498237887118777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-525152041671202352290381819615800000000000000)
      constant := (3263628388130431554478155366104874430377122127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree021.table
  base := (-10597689095913514951286344572600816338713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-3740961810777548034734341000200000000000000)
      constant := (23422348034942449624430873965419333876564247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/50000000000000000000)
  centralHi := (222992492199857323707/100000000000000000000)
  directionLo := (114249654437528388551/50000000000000000000)
  directionHi := (228499308875056777103/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree022.table
  base := (-11048368720497977363936820657746698314781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-546356504636041900362375388095000000000000000)
      constant := (3543009045926493581920469144673058050994072331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree022.table
  base := (-2222903813549288583784496095048557873861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-35029788818843264837643579915000000000000000)
      constant := (228871167972047274699594519084148006549776655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114249654437528388551/50000000000000000000)
  centralHi := (228499308875056777103/100000000000000000000)
  directionLo := (46775299778944772591/20000000000000000000)
  directionHi := (58469124723680965739/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree023.table
  base := (-11459927810682232871800207613537317223219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-567560967600881448434368956574200000000000000)
      constant := (3834994750377294745664279674360811255111365669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree023.table
  base := (-5758989504752442879950596492947316022941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-18195460670344298681339045414100000000000000)
      constant := (123877414479041684951896298700241406619276011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46775299778944772591/20000000000000000000)
  centralHi := (58469124723680965739/25000000000000000000)
  directionLo := (47826561370907251859/20000000000000000000)
  directionHi := (7472900214204258103/3125000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree024.table
  base := (-11766778793502068282791184039094490239229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-588765430565720996506362525053400000000000000)
      constant := (4139475093360487362948618258408407181251067179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree024.table
  base := (-2363525845444912874458043785011993810157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-4194672651392658876412511304600000000000000)
      constant := (29716127312165587966420080055070142506886415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47826561370907251859/20000000000000000000)
  centralHi := (7472900214204258103/3125000000000000000)
  directionLo := (12213801813215665899/5000000000000000000)
  directionHi := (244276036264313317981/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree025.table
  base := (-5988505979325781020168858894829217792613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-304984946765280272289178046766300000000000000)
      constant := (2228178724574681964837339046420600285492373763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree025.table
  base := (-6010739574283074963394784083186731687403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-19556593192189631206373556327300000000000000)
      constant := (143968139826751705399059290585856872599883213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/5000000000000000000)
  centralHi := (244276036264313317981/100000000000000000000)
  directionLo := (249313185515486297743/100000000000000000000)
  directionHi := (15582074094717893609/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree026.table
  base := (-12097418408606017599996420159005979006173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-631174356495400092650349662011800000000000000)
      constant := (4785564066411684696579791534956740546358325323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree026.table
  base := (-3034060580733912888430292897936522085349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-10118579726556148734445405891950000000000000)
      constant := (77305834078151436637200372953954275399780579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249313185515486297743/100000000000000000000)
  centralHi := (15582074094717893609/6250000000000000000)
  directionLo := (50850111917577706807/20000000000000000000)
  directionHi := (63562639896972133509/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree027.table
  base := (-189589073303458049338004384779735798807/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-81547352432529955090292903811375000000000000)
      constant := (640878707084344736412687540026579438715669256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree027.table
  base := (-12167547853958574940095965707389606612313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1100)
      square := (46935604201563190518431410800000000000000)
      linear := (-1549461164002589906030227203000000000000000)
      constant := (12270452302602011307555499248700480621467549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50850111917577706807/20000000000000000000)
  centralHi := (63562639896972133509/25000000000000000000)
  directionLo := (64773465646450104483/25000000000000000000)
  directionHi := (259093862585800417933/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree028.table
  base := (-12090648329638770762979049402231761930653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-673583282425079188794336798970200000000000000)
      constant := (5480699384695007986386402742433048557655953803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree028.table
  base := (-12120116484961573305147213869691257733663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-43196583949915259987850645394200000000000000)
      constant := (354169465804563956866888495882195073112159673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64773465646450104483/25000000000000000000)
  centralHi := (259093862585800417933/100000000000000000000)
  directionLo := (263848274977314947571/100000000000000000000)
  directionHi := (65962068744328736893/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree029.table
  base := (-2394456909426908231540788765679601630043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-694787745389918736866330367449400000000000000)
      constant := (5846527188582276863299150830287671204688188465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree029.table
  base := (-11997907652742166542173758015853148282147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-44557716471760592512885156307400000000000000)
      constant := (377822210786109309235256684545443054902314837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263848274977314947571/100000000000000000000)
  centralHi := (65962068744328736893/25000000000000000000)
  directionLo := (134259259259259259259/50000000000000000000)
  directionHi := (268518518518518518519/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree030.table
  base := (-11781989156817017241549712670626585655129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-715992208354758284938323935928600000000000000)
      constant := (6224474372858576354628589853151996220834428079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree030.table
  base := (-11804242507384524487981904150701987396427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-5102094332622880559768851913400000000000000)
      constant := (44695336221831000288674583180793139020889413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134259259259259259259/50000000000000000000)
  centralHi := (268518518518518518519/100000000000000000000)
  directionLo := (273108911180604182117/100000000000000000000)
  directionHi := (136554455590302091059/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree031.table
  base := (-11522601606260910690261471871513921157681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-737196671319597833010317504407800000000000000)
      constant := (6614508428688623586399113978599237116665710231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree031.table
  base := (-2885476733927321071838722633601822737041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-11819995378862814390738544533450000000000000)
      constant := (106868720131045198119196301858904271224697111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273108911180604182117/100000000000000000000)
  centralHi := (136554455590302091059/50000000000000000000)
  directionLo := (8675731684354716357/3125000000000000000)
  directionHi := (11104936555974036937/4000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree032.table
  base := (-559825372486242240437195867457165152821/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-189600283571109345270577768221750000000000000)
      constant := (1754150510965427895098217335765814580826761855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree032.table
  base := (-5606618947704874604073177285852557472029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-24320557018648295043994344523500000000000000)
      constant := (226735535363528130394566629651413485602890859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8675731684354716357/3125000000000000000)
  centralHi := (11104936555974036937/4000000000000000000)
  directionLo := (35258208823444019841/12500000000000000000)
  directionHi := (282065670587552158729/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree033.table
  base := (-84419616764891313892240288928595044769/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-97450699656159616144288080170775000000000000)
      constant := (928841533952501913577948250129179245319035504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree033.table
  base := (-10820195792795260684346538285645181806863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-5555805173237991401447022217800000000000000)
      constant := (53360574163211766403304057532662740273644097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/12500000000000000000)
  centralHi := (282065670587552158729/100000000000000000000)
  directionLo := (11457561702413347837/4000000000000000000)
  directionHi := (143219521280166847963/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree034.table
  base := (-2587974006267779746768767103020436620223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-200202515053529119306574552461350000000000000)
      constant := (1964219958161478465577996309654019021135066873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree034.table
  base := (-1295553146927569093788590221365452506119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-12840844770246813784514427718350000000000000)
      constant := (126948992968640575471887860429999170246078498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11457561702413347837/4000000000000000000)
  centralHi := (143219521280166847963/50000000000000000000)
  directionLo := (290746638298288549453/100000000000000000000)
  directionHi := (145373319149144274727/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree035.table
  base := (-4918238748993060859069276122418229777071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-411007261589478012649145889162300000000000000)
      constant := (4147514264385472597657303886774933687282314121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree035.table
  base := (-9847305633937047963737934094304579381001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-52724511602832587663092221786600000000000000)
      constant := (536122478222440586518011064891251961631250271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290746638298288549453/100000000000000000000)
  centralHi := (145373319149144274727/50000000000000000000)
  directionLo := (147495669648833251239/50000000000000000000)
  directionHi := (294991339297666502479/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree036.table
  base := (-1157580509156783134858714030623142227369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-105402373267974446671285668350475000000000000)
      constant := (1093145593808788953637450113780295644638852319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree036.table
  base := (-9269994496619436769349574003719746443517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1100)
      square := (46935604201563190518431410800000000000000)
      linear := (-2003172004617700747708397507400000000000000)
      constant := (20934216400749203784700661541499566846025041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147495669648833251239/50000000000000000000)
  centralHi := (294991339297666502479/100000000000000000000)
  directionLo := (299175822618583557291/100000000000000000000)
  directionHi := (74793955654645889323/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree037.table
  base := (-2156348623970476646343829329921477433261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-216105862277158780360569728820750000000000000)
      constant := (2301819265778108844116264562868879004866594811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree037.table
  base := (-8633462641976874883439140573607649924847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-55446776646523252713161243613000000000000000)
      constant := (595099357897492874377092413082440023204786537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299175822618583557291/100000000000000000000)
  centralHi := (74793955654645889323/25000000000000000000)
  directionLo := (303302580632577777457/100000000000000000000)
  directionHi := (151651290316288888729/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree038.table
  base := (-1982891977078072664776021683978010794587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-221406978018368667378568120940550000000000000)
      constant := (2420338964838870933007453352590435754412773437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree038.table
  base := (-7938524539808275977066165701115818492453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-56807909168368585238195754526200000000000000)
      constant := (625748429705750295022332320524086568319001763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303302580632577777457/100000000000000000000)
  centralHi := (151651290316288888729/50000000000000000000)
  directionLo := (307373938383293185429/100000000000000000000)
  directionHi := (30737393838329318543/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree039.table
  base := (-7179869358249862497339001111134448198347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-906832375038314217586266052241400000000000000)
      constant := (10167393067108288502730173541811621702577125197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree039.table
  base := (-7185863451391108462260444224387272138601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-6463226854468213084803362826600000000000000)
      constant := (73018951127503276627807540389824630956773319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307373938383293185429/100000000000000000000)
  centralHi := (30737393838329318543/10000000000000000000)
  directionLo := (311392068903708090641/100000000000000000000)
  directionHi := (155696034451854045321/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree040.table
  base := (-3185445614700157919476857408447342952123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-464018419001576882829129810360300000000000000)
      constant := (5332690952084901600474887088462686370541143773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree040.table
  base := (-24906455348233704234321334574286936391/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-14882543553014812572066194088150000000000000)
      constant := (172341332841388621969255019475102068695741504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311392068903708090641/100000000000000000000)
  centralHi := (155696034451854045321/50000000000000000000)
  directionLo := (315359006776414836409/100000000000000000000)
  directionHi := (31535900677641483641/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree041.table
  base := (-5505131246968134833889867497443735677389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-949241300967993313730253189199800000000000000)
      constant := (11175316672084161687655933483415966670229573339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree041.table
  base := (-1101914550041174865950156031418174391519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-60891306733904582813299287265800000000000000)
      constant := (722332392814979386753596242473680754342913245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315359006776414836409/100000000000000000000)
  centralHi := (31535900677641483641/10000000000000000000)
  directionLo := (159638330088580253679/50000000000000000000)
  directionHi := (319276660177160507359/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree042.table
  base := (-916601521090374290024004412740428232199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-970445763932832861802246757679000000000000000)
      constant := (11697192582942550041367333588516274185847768245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree042.table
  base := (-4586827392727662487888555953830112640049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-6916937695083323926481533131000000000000000)
      constant := (84007938935393753899711162861139760876156031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159638330088580253679/50000000000000000000)
  centralHi := (319276660177160507359/100000000000000000000)
  directionLo := (161573410801992109247/50000000000000000000)
  directionHi := (64629364320796843699/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree043.table
  base := (-901217919676677904750964173466059279879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-247912556724418102468560081539550000000000000)
      constant := (3057751403466425059588959384191037087304665329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree043.table
  base := (-360815491540266829955527105918749843723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-31806785888797623931684154546100000000000000)
      constant := (395291128734511527619465127769526156819629665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161573410801992109247/50000000000000000000)
  centralHi := (64629364320796843699/20000000000000000000)
  directionLo := (65394235492628055683/20000000000000000000)
  directionHi := (20435698591446267401/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree044.table
  base := (-2571018698700280786425019479658411383091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1012854689862511957946233894637400000000000000)
      constant := (12776752384742814934891523441157390848074991141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree044.table
  base := (-1286919613145806402924037065189984044919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-32487352149720290194201410002700000000000000)
      constant := (412932303498720465769612895234476501631254049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65394235492628055683/20000000000000000000)
  centralHi := (20435698591446267401/6250000000000000000)
  directionLo := (66150263331450932201/20000000000000000000)
  directionHi := (165375658328627330503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree045.table
  base := (-1481696727613877029635899977012862662547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1034059152827351506018227463116600000000000000)
      constant := (13334430055509980449287928693670179735376499397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree045.table
  base := (-371029626244753270007266024348661963057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (319)
      previous := (0)
      next := (275)
      square := (11733901050390797629607852700000000000000)
      linear := (-614220711308202897346641952950000000000000)
      constant := (7980725234915558343072953707592586126997461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66150263331450932201/20000000000000000000)
  centralHi := (165375658328627330503/50000000000000000000)
  directionLo := (334488738299785985559/100000000000000000000)
  directionHi := (8362218457494649639/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree046.table
  base := (-337114196048374183782834566158514765651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1055263615792191054090221031595800000000000000)
      constant := (13904036239845247377006462889085251164448061701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree046.table
  base := (-339192569790063542328949400580212926527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-67696969343131245438471841831800000000000000)
      constant := (898743266921782097044541698939177024776561817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334488738299785985559/100000000000000000000)
  centralHi := (8362218457494649639/2500000000000000000)
  directionLo := (4227310733275387567/1250000000000000000)
  directionHi := (338184858662031005361/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree047.table
  base := (862553763501337702073695175559908210769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1076468078757030602162214600075000000000000000)
      constant := (14485568932656681721875432573823585389105094281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree047.table
  base := (172154188391784962388227958908759899207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-69058101864976577963506352745000000000000000)
      constant := (936339309442542728801632072135822429832609515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4227310733275387567/1250000000000000000)
  centralHi := (338184858662031005361/100000000000000000000)
  directionLo := (68368203488795303867/20000000000000000000)
  directionHi := (42730127180497064917/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree048.table
  base := (211715999536551877433179079421648007667/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-548836270860935075117104084277100000000000000)
      constant := (7539513224579510316155474806243092240198897415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree048.table
  base := (264453923679716992540969376487635313993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (957)
      previous := (0)
      next := (825)
      square := (35201703151172392888823558100000000000000)
      linear := (-1956089844078386402459468434950000000000000)
      constant := (27075176400166582467450043224190996920866866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368203488795303867/20000000000000000000)
  centralHi := (42730127180497064917/12500000000000000000)
  directionLo := (21591155215483368161/6250000000000000000)
  directionHi := (345458483447733890577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree049.table
  base := (53540325778844421861088610020795887203/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-139859625585838712288275217129175000000000000)
      constant := (1960550921710858782918887686444899736900697176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree049.table
  base := (342527077908018287886940129340089402901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-35890183454333621506787687285700000000000000)
      constant := (506922151897417533413761110459944625873574145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/6250000000000000000)
  centralHi := (345458483447733890577/100000000000000000000)
  directionLo := (8725961493042020421/2500000000000000000)
  directionHi := (349038459721680816841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree050.table
  base := (598839053359639215617865081028358589171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-142510183456443655797274413189075000000000000)
      constant := (2037713814586047163641659015078943677487418779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree050.table
  base := (2394795058041559601043662701537530445909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-36570749715256287769304942742300000000000000)
      constant := (526876548720922764527710027786920859695067661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8725961493042020421/2500000000000000000)
  centralHi := (349038459721680816841/100000000000000000000)
  directionLo := (35258208823444019841/10000000000000000000)
  directionHi := (352582088234440198411/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree051.table
  base := (31047337100042299858038416874632045949/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-145160741327048599306273609248975000000000000)
      constant := (2116366859823999077150609821201466557351752525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree051.table
  base := (6208506343729655996171135466265152823431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-8278070216928656451516044044200000000000000)
      constant := (121603630088742415943747476039567477378697911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35258208823444019841/10000000000000000000)
  centralHi := (352582088234440198411/100000000000000000000)
  directionLo := (356090454130174268641/100000000000000000000)
  directionHi := (178045227065087134321/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree052.table
  base := (7682772464769015492994780687366921863297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1182490393581228342522182442471000000000000000)
      constant := (17572079619447886950114216853463263888412887353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree052.table
  base := (3840974887914517137294540333672292471279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-37931882237101620294339453655500000000000000)
      constant := (567941486532055323420631130461047101211562391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356090454130174268641/100000000000000000000)
  centralHi := (178045227065087134321/50000000000000000000)
  directionLo := (179782294805070360357/50000000000000000000)
  directionHi := (71912917922028144143/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree053.table
  base := (9210565910802217380738032623164782293929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1203694856546067890594176010950200000000000000)
      constant := (18225144033421128019123402577796813592483193121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree053.table
  base := (9209861942824359204407565963686066279747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-77224896996048573113713418224200000000000000)
      constant := (1178103961613825262764816394485727142317935563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179782294805070360357/50000000000000000000)
  centralHi := (71912917922028144143/20000000000000000000)
  directionLo := (363005477479864052521/100000000000000000000)
  directionHi := (181502738739932026261/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree054.table
  base := (2698198987511677187464086104074438116891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-306224829877726859666542394857350000000000000)
      constant := (4722531881840305337314071797159048242000285059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree054.table
  base := (10792193784919764866689522535713273615507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1100)
      square := (46935604201563190518431410800000000000000)
      linear := (-2910593685847922431064738116200000000000000)
      constant := (45225762988267940926277205995464258387618689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363005477479864052521/100000000000000000000)
  centralHi := (181502738739932026261/50000000000000000000)
  directionLo := (36641405439646997697/10000000000000000000)
  directionHi := (366414054396469976971/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree055.table
  base := (2485883808812005465084093288237071661811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1246103782475746986738163147908600000000000000)
      constant := (19567029602796539189927205707018131167280370695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree055.table
  base := (3107226034079158071730675791399437384539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-19986790509934809540945610012650000000000000)
      constant := (316214465065617720085711833718930189853328931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36641405439646997697/10000000000000000000)
  centralHi := (366414054396469976971/100000000000000000000)
  directionLo := (184895606923294983087/50000000000000000000)
  directionHi := (14791648553863598647/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree056.table
  base := (7060199301338423822901289008347266357177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-633654122720293267405078358193900000000000000)
      constant := (10127924920403139364962990606982167852523319473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree056.table
  base := (14119958453656494822522457309838132388341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-81308294561584570688816950963800000000000000)
      constant := (1309390715169426366582460503234071998511100589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184895606923294983087/50000000000000000000)
  centralHi := (14791648553863598647/4000000000000000000)
  directionLo := (373137808881664526229/100000000000000000000)
  directionHi := (37313780888166452623/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree057.table
  base := (15865703873833969431926806571301717967147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1288512708405426082882150284867000000000000000)
      constant := (20956587889310068389257474044403433369005866003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree057.table
  base := (7932663874662482477356804264404685741319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-4592745949079439067436192326500000000000000)
      constant := (75260785792896109734840942407116779545046839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373137808881664526229/100000000000000000000)
  centralHi := (37313780888166452623/10000000000000000000)
  directionLo := (376454654634372629193/100000000000000000000)
  directionHi := (188227327317186314597/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree058.table
  base := (3533061802162755324976856332736347565217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1309717171370265630954143853346200000000000000)
      constant := (21669243452388838181663236540652692216370847165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree058.table
  base := (2208123462076278578192028145571165110507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-21007639901318808934721493197550000000000000)
      constant := (350192032459102198457155981244792758731119206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376454654634372629193/100000000000000000000)
  centralHi := (188227327317186314597/50000000000000000000)
  directionLo := (379742530637219966807/100000000000000000000)
  directionHi := (47467816329652495851/12500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree059.table
  base := (19519192288551478674139793804941192432383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1330921634335105179026137421825400000000000000)
      constant := (22393816281312321320130191089273771712158352967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree059.table
  base := (19518917879027529155339836454447805508663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-85391692127120568263920483703400000000000000)
      constant := (1447612656978645434767456195001292450215815327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379742530637219966807/100000000000000000000)
  centralHi := (47467816329652495851/12500000000000000000)
  directionLo := (191501091480985504981/50000000000000000000)
  directionHi := (383002182961971009963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree060.table
  base := (21427335445183048469023054319479260264889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1352126097299944727098130990304600000000000000)
      constant := (23130306167000436558268273555219718050772714161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree060.table
  base := (21427101160582151943840401109631587161401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-9639202738773988976550554957400000000000000)
      constant := (166136412578522194566669634143880158560073481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191501091480985504981/50000000000000000000)
  centralHi := (383002182961971009963/100000000000000000000)
  directionLo := (386234326196559448249/100000000000000000000)
  directionHi := (1544937304786237793/400000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree061.table
  base := (23389723128818147391384264406975959400437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1373330560264784275170124558783800000000000000)
      constant := (23878712933689391409238286892025667759175603213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree061.table
  base := (292369039468572030428910707121015177031/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-22028489292702808328497376382450000000000000)
      constant := (385903322008697511733620722813374401281111980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386234326196559448249/100000000000000000000)
  centralHi := (1544937304786237793/400000000000000000)
  directionLo := (77887929054863298383/20000000000000000000)
  directionHi := (97359911318579122979/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree062.table
  base := (25406342432721219457726337546816620109871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1394535023229623823242118127263000000000000000)
      constant := (24639036433609970492585172956117103483637913079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree062.table
  base := (2540617179498034256626424371459221824837/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-44737544846328282919512008221500000000000000)
      constant := (796384686330208863552362689839268863551530865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77887929054863298383/20000000000000000000)
  centralHi := (97359911318579122979/25000000000000000000)
  directionLo := (196309398584390650031/50000000000000000000)
  directionHi := (392618797168781300063/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree063.table
  base := (5495436500954317695753451348703492752171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1415739486194463371314111695742200000000000000)
      constant := (25411276542516244186617841934912731442598028895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree063.table
  base := (13738518467778779018265524595433832303529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (638)
      previous := (0)
      next := (550)
      square := (23467802100781595259215705400000000000000)
      linear := (-1682152263231516636371454210300000000000000)
      constant := (30420295549876652146365703172876713472195283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196309398584390650031/50000000000000000000)
  centralHi := (392618797168781300063/100000000000000000000)
  directionLo := (395772412465972421357/100000000000000000000)
  directionHi := (197886206232986210679/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree064.table
  base := (29602234219331508639142484165621204949597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1436943949159302919386105264221400000000000000)
      constant := (26195433155928785939496185234780197175467936053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree064.table
  base := (29602110067070662256661620121598520903367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-92197354736347230889093038269400000000000000)
      constant := (1693393042928199535068569411276645321738554543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395772412465972421357/100000000000000000000)
  centralHi := (197886206232986210679/50000000000000000000)
  directionLo := (99725274206194519097/25000000000000000000)
  directionHi := (398901096824778076389/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree065.table
  base := (7945372475387086636753943147687718703579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-364537103031035616864524708175150000000000000)
      constant := (6747876546494551987879267415317626691437275971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree065.table
  base := (794534601027234144447801925600574811927/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-23389621814548140853531887295650000000000000)
      constant := (436215154288448250897763852839878190378947830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99725274206194519097/25000000000000000000)
  centralHi := (398901096824778076389/100000000000000000000)
  directionLo := (201002716167522314283/50000000000000000000)
  directionHi := (402005432335044628567/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree066.table
  base := (34014943095711087607645723848311540740083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1479352875088982015530092401179800000000000000)
      constant := (27799495558753074816585300946728518829933210267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree066.table
  base := (34014852853402820956927051876757020794219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-10546624420004210659906895566200000000000000)
      constant := (199677630888116657059911100921817318684331739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201002716167522314283/50000000000000000000)
  centralHi := (402005432335044628567/100000000000000000000)
  directionLo := (81017195756397620917/20000000000000000000)
  directionHi := (202542989390994052293/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree067.table
  base := (36302588370620620086638050783562599570429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1500557338053821563602085969659000000000000000)
      constant := (28619401212071587904453798897519608202481841621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree067.table
  base := (18151255729940049989877290978195352697209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-48140376150941614232098285504500000000000000)
      constant := (925053610884399409268315960630904412116265361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81017195756397620917/20000000000000000000)
  centralHi := (202542989390994052293/50000000000000000000)
  directionLo := (408143274824707222371/100000000000000000000)
  directionHi := (102035818706176805593/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree068.table
  base := (38644421156058470616397307264438442134811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1521761801018661111674079538138200000000000000)
      constant := (29451223093609315913536963250877755724001451139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree068.table
  base := (19322177810995819139359705220935828157541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-48820942411864280494615540961100000000000000)
      constant := (951943122695575833006758094016662218726847389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408143274824707222371/100000000000000000000)
  centralHi := (102035818706176805593/25000000000000000000)
  directionLo := (411177839095824399231/100000000000000000000)
  directionHi := (3212326867936128119/781250000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree069.table
  base := (1641617504215362103826155387594206206669/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1542966263983500659746073106617400000000000000)
      constant := (30294961159326070767836858257929151671503834525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree069.table
  base := (41040381777212930861882906175476668818033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-11000335260619321501585065870600000000000000)
      constant := (217603971807003121314525494055213610174260673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411177839095824399231/100000000000000000000)
  centralHi := (3212326867936128119/781250000000000000)
  directionLo := (414190171228611883481/100000000000000000000)
  directionHi := (207095085614305941741/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree070.table
  base := (8698126896016956898163672286161561711699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1564170726948340207818066675096600000000000000)
      constant := (31150615372144121921375418630443318600186209255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree070.table
  base := (135908084157192835837432450200063488027/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-25091037466854806509825025937150000000000000)
      constant := (503438930550224120241952070804917702621734640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414190171228611883481/100000000000000000000)
  centralHi := (207095085614305941741/50000000000000000000)
  directionLo := (417180752817363330889/100000000000000000000)
  directionHi := (41718075281736333089/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree071.table
  base := (45995009052770785822668213415956227296221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1585375189913179755890060243575800000000000000)
      constant := (32018185700837582632546025690327482846314434229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree071.table
  base := (1437342767565178101506193456922286763021/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-25431320597316139641083653665450000000000000)
      constant := (517461542842070062358492979702570776401938472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417180752817363330889/100000000000000000000)
  centralHi := (41718075281736333089/10000000000000000000)
  directionLo := (420150048316238057541/100000000000000000000)
  directionHi := (210075024158119028771/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree072.table
  base := (3034597439104159551288898104046356647271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-200822456609752412995256726506875000000000000)
      constant := (4112209014887402644834912094490653474509211358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree072.table
  base := (24276762276469965858446531967863811595817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (638)
      previous := (0)
      next := (550)
      square := (23467802100781595259215705400000000000000)
      linear := (-1909007683539072057210539362500000000000000)
      constant := (39383464670740236867207074839532322913087059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420150048316238057541/100000000000000000000)
  centralHi := (210075024158119028771/50000000000000000000)
  directionLo := (105774626470332059523/25000000000000000000)
  directionHi := (423098505881328238093/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree073.table
  base := (25583141231061549578853637475942202626301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-813892057921429426017023690267100000000000000)
      constant := (16894537302378171627658855796731162277868520149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree073.table
  base := (51166253118587002681304663736618919551593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-104447547432955223614403636488200000000000000)
      constant := (2184338483455235878954917820736195192353111297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105774626470332059523/25000000000000000000)
  centralHi := (423098505881328238093/100000000000000000000)
  directionLo := (17041062326410875123/4000000000000000000)
  directionHi := (106506639540067969519/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree074.table
  base := (53833177729069841432830375178204711735097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1648988578807698400106040949013400000000000000)
      constant := (34692393139111923813102161551057265744655125553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree074.table
  base := (26916576378117547530270094798155503452133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-52904339977400278069719073700700000000000000)
      constant := (1121370171989267139579604202751355362016604957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17041062326410875123/4000000000000000000)
  centralHi := (106506639540067969519/25000000000000000000)
  directionLo := (428934623033350723023/100000000000000000000)
  directionHi := (26808413939584420189/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree075.table
  base := (7069280431082255860864012023117650790063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-208774130221567243522254314686575000000000000)
      constant := (4450953463298871586334243073020798983895431287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree075.table
  base := (28277111099694166047909080662323925350197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-5953878470924771592470703239700000000000000)
      constant := (127884037381477360960272338698648237953365957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428934623033350723023/100000000000000000000)
  centralHi := (26808413939584420189/6250000000000000000)
  directionLo := (21591155215483368161/5000000000000000000)
  directionHi := (431823104309667363221/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree076.table
  base := (29664739228813525957946064814441182096963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-845698752368688748125014042985900000000000000)
      constant := (18267389146637659275215087111284137093828129387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree076.table
  base := (29664730189966202279331188689646951113577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-54265472499245610594753584613900000000000000)
      constant := (1180927734670377600952219871515352627361797633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21591155215483368161/5000000000000000000)
  centralHi := (431823104309667363221/100000000000000000000)
  directionLo := (217346196190842635799/50000000000000000000)
  directionHi := (434692392381685271599/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree077.table
  base := (62158881773159198247796233920882494011723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1712601967702217044322021654451000000000000000)
      constant := (37473844888512682022815017374308783673940216627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree077.table
  base := (6215886639632348954748632458240669503999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-54946038760168276857270840070500000000000000)
      constant := (1211284366371898473061282388380587240342076355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217346196190842635799/50000000000000000000)
  centralHi := (434692392381685271599/100000000000000000000)
  directionLo := (218771432420567769967/50000000000000000000)
  directionHi := (87508572968227107987/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree078.table
  base := (32521226282093327826823647916134670749253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-866903215333528296197007611465100000000000000)
      constant := (19212413741294083759768457535016425845408197597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree078.table
  base := (3252121974344865193768200635200524833493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (957)
      previous := (0)
      next := (825)
      square := (35201703151172392888823558100000000000000)
      linear := (-3090366945616163506654894195950000000000000)
      constant := (69001457292235124097111337524706212557564665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218771432420567769967/50000000000000000000)
  centralHi := (87508572968227107987/20000000000000000000)
  directionLo := (440374887059041293017/100000000000000000000)
  directionHi := (220187443529520646509/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree079.table
  base := (67980190127279001684929764503652117061573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1755010893631896140466008791409400000000000000)
      constant := (39387726067448200133982812767951313088237949277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree079.table
  base := (67980179007473535167686566620902021832271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-112614342564027218764610701967400000000000000)
      constant := (2546306658201150318303679995450637573915725559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440374887059041293017/100000000000000000000)
  centralHi := (220187443529520646509/50000000000000000000)
  directionLo := (443188812732382208033/100000000000000000000)
  directionHi := (221594406366191104017/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree080.table
  base := (3548604693318982391312288361102823861687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-444053839149183922134500589972150000000000000)
      constant := (10090635159067131996059980055843331151962272315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree080.table
  base := (35486042206281886212029167158915170096713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-56987737542936275644822606440300000000000000)
      constant := (1304665659694096723463145940062849159000503777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443188812732382208033/100000000000000000000)
  centralHi := (221594406366191104017/50000000000000000000)
  directionLo := (111496246099928661853/25000000000000000000)
  directionHi := (445984984399714647413/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree081.table
  base := (925227040947202126910012331943007340299/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-224677477445196904576249491045975000000000000)
      constant := (5168658897907406191099158412002429910390832510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree081.table
  base := (37009077619801263497832861420809739242111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (638)
      previous := (0)
      next := (550)
      square := (23467802100781595259215705400000000000000)
      linear := (-2135863103846627478049624514700000000000000)
      constant := (49502341587858955780349235104661862959536997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111496246099928661853/25000000000000000000)
  centralHi := (445984984399714647413/100000000000000000000)
  directionLo := (448763733927875335937/100000000000000000000)
  directionHi := (224381866963937667969/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree082.table
  base := (77118397925787877172979867975490219295047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1818624282526414784681989496847000000000000000)
      constant := (42347917703500950530755347502094987520708993103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree082.table
  base := (4819899443482152762493975991857299178191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1822500000000000000000000000000000000000000
      center := (8613)
      previous := (0)
      next := (7425)
      square := (316815328360551535999412022900000000000000)
      linear := (-29174435032390804084928558676750000000000000)
      constant := (684423009245828670094440328057405884403604956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448763733927875335937/100000000000000000000)
  centralHi := (224381866963937667969/50000000000000000000)
  directionLo := (451525382971726253267/100000000000000000000)
  directionHi := (112881345742931563317/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree083.table
  base := (2508524920335516117582768486404420054327/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-229978593186406791594247883165775000000000000)
      constant := (5419810024100872583763494092170901820807959292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree083.table
  base := (40136395823304624433179946904696061567033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-59029436325704274432374372810100000000000000)
      constant := (1401514046430644520521884647338123428882367057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451525382971726253267/100000000000000000000)
  centralHi := (112881345742931563317/25000000000000000000)
  directionLo := (454270243408743681079/100000000000000000000)
  directionHi := (11356756085218592027/2500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree084.table
  base := (521758509617721176244563957411632055483/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-232629151057011735103247079225675000000000000)
      constant := (5547619830950961755578019362172615508064497340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree084.table
  base := (8348135660726177247260536805828496675379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-6634444731847437854987958696300000000000000)
      constant := (159396367398362408126890653583360541153528495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454270243408743681079/100000000000000000000)
  centralHi := (11356756085218592027/2500000000000000000)
  directionLo := (91399723550022710841/20000000000000000000)
  directionHi := (228499308875056777103/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree085.table
  base := (21686022480922609581587291298718419175413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-470559417855233357224492550571150000000000000)
      constant := (11353838266213286276343261030311777181139303437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree085.table
  base := (86744085734089611556377256110037569381249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-120781137695099213914817767446600000000000000)
      constant := (2936011597733446023974559153255217388078930521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91399723550022710841/20000000000000000000)
  centralHi := (228499308875056777103/50000000000000000000)
  directionLo := (229855399764933505227/50000000000000000000)
  directionHi := (91942159905973402091/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree086.table
  base := (90060982377155834802440619305874858843427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1903442134385772976969963770763800000000000000)
      constant := (46461663441931292229321610676858161258898395723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree086.table
  base := (90060978818387275052278646518883900470709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-122142270216944546439852278359800000000000000)
      constant := (3003659046397910771128677112496466363443146861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229855399764933505227/50000000000000000000)
  centralHi := (91942159905973402091/20000000000000000000)
  directionLo := (7225110526148016629/1562500000000000000)
  directionHi := (462407073673473064257/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree087.table
  base := (46716019351663861484595421853903131393/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (67089)
      previous := (0)
      next := (58850)
      square := (2487804317146745223358894547450000000000000)
      linear := (-240580824668826565630244667405375000000000000)
      constant := (5939986222074904023060995664966159237829614250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree087.table
  base := (46716017840407262563494783491724694984129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1914)
      previous := (0)
      next := (1650)
      square := (70403406302344785777647116200000000000000)
      linear := (-6861300152154993275827043848500000000000000)
      constant := (170670942168509919686994187912029700293714449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7225110526148016629/1562500000000000000)
  centralHi := (462407073673473064257/100000000000000000000)
  directionLo := (465087716847198532521/100000000000000000000)
  directionHi := (232543858423599266261/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree088.table
  base := (96857258733494384970704032766576686054219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1945851060315452073113950907722200000000000000)
      constant := (48590032066925384513139956971155736478634753331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree088.table
  base := (96857256166769204115746948688657753355631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-124864535260635211489921300186200000000000000)
      constant := (3141265335526544400748601685849231502196254999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465087716847198532521/100000000000000000000)
  centralHi := (232543858423599266261/50000000000000000000)
  directionLo := (467752997789447725911/100000000000000000000)
  directionHi := (58469124723680965739/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree089.table
  base := (25084160580472522814008173856074447602809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-491763880820072905296486119050350000000000000)
      constant := (12418022577810219344412196951503946350604560241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree089.table
  base := (100336640142502177741995359424195006412139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-126225667782480544014955811099400000000000000)
      constant := (3211224175780505191389187112713238159674449331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467752997789447725911/100000000000000000000)
  centralHi := (58469124723680965739/12500000000000000000)
  directionLo := (94080635525041020129/20000000000000000000)
  directionHi := (235201588812602550323/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree090.table
  base := (20774037868424865696915449011181854326687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-1988259986245131169257938044680600000000000000)
      constant := (50766064508098665790777933157039105250931197315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree090.table
  base := (51935093745927478947831288151953953730751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (638)
      previous := (0)
      next := (550)
      square := (23467802100781595259215705400000000000000)
      linear := (-2362718524154182898888709666900000000000000)
      constant := (60776916290932988675100166898602756750730277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94080635525041020129/20000000000000000000)
  centralHi := (235201588812602550323/50000000000000000000)
  directionLo := (236519255082311127307/50000000000000000000)
  directionHi := (94607702032924450923/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree091.table
  base := (26864474921044647738349832497501337476787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (134178)
      previous := (0)
      next := (117700)
      square := (4975608634293490446717789094900000000000000)
      linear := (-502366112302492679332482903289950000000000000)
      constant := (12967988664059786970183612958984942812771734363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree091.table
  base := (107457898113519806513461320797295890612131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-128947932826171209065024832925800000000000000)
      constant := (3353453247242319650899130959234428704256243499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236519255082311127307/50000000000000000000)
  centralHi := (94607702032924450923/20000000000000000000)
  directionLo := (95131848437343127989/20000000000000000000)
  directionHi := (237829621093357819973/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree092.table
  base := (22219954650376029651550719807470887808229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-2030668912174810265401925181639000000000000000)
      constant := (52989760754561242057114414316952270972582069105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree092.table
  base := (55549885959369130432207600369347262993137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-65154532674008270795029671919500000000000000)
      constant := (1712861739155807529694735581477054154721996873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95131848437343127989/20000000000000000000)
  centralHi := (237829621093357819973/50000000000000000000)
  directionLo := (478265613709072518591/100000000000000000000)
  directionHi := (7472900214204258103/1562500000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree093.table
  base := (114795809960776674640914274175450024818411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-2051873375139649813473918750118200000000000000)
      constant := (54119482802098053642329067167496927334145987539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree093.table
  base := (22959161765873511838676562143463656900647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-14630021985540208235010428305800000000000000)
      constant := (388751574762366837845214615459902781044762035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478265613709072518591/100000000000000000000)
  centralHi := (7472900214204258103/1562500000000000000)
  directionLo := (480857858244399440013/100000000000000000000)
  directionHi := (240428929122199720007/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree094.table
  base := (118546009736347785353647389448153205200519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-2073077838104489361545912318597400000000000000)
      constant := (55261120797996398751384430711341906046340742031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree094.table
  base := (23709201755251160629588350411657243734581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-133031330391707206640128365665400000000000000)
      constant := (3572575330840967360652596159155490653412547745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480857858244399440013/100000000000000000000)
  centralHi := (240428929122199720007/50000000000000000000)
  directionLo := (24171810152234467997/5000000000000000000)
  directionHi := (483436203044689359941/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree095.table
  base := (61175186256249870988314336424887353285399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-1047141150534664454808952943538300000000000000)
      constant := (28207337370749785086558830679147035307764533151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree095.table
  base := (122350371697876221142692029780032451371469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7290000000000000000000000000000000000000000
      center := (34452)
      previous := (0)
      next := (29700)
      square := (1267261313442206143997648091600000000000000)
      linear := (-134392462913552539165162876578600000000000000)
      constant := (3647156952205759503040708426661643657049800901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24171810152234467997/5000000000000000000)
  centralHi := (483436203044689359941/100000000000000000000)
  directionLo := (243000434666864993983/50000000000000000000)
  directionHi := (486000869333729987967/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree096.table
  base := (126208898230298172630801744248416322246341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-2115486764034168457689899455555800000000000000)
      constant := (57580144631932828283885442612223318473398358109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree096.table
  base := (126208897539178889608764171875882336880977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3828)
      previous := (0)
      next := (3300)
      square := (140806812604689571555294232400000000000000)
      linear := (-15083732826155319076688598610200000000000000)
      constant := (413612115212838508165506944062746469287359137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243000434666864993983/50000000000000000000)
  centralHi := (486000869333729987967/100000000000000000000)
  directionLo := (12213801813215665899/2500000000000000000)
  directionHi := (488552072528626635961/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree097.table
  base := (104097269469520692195379522360233369209/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (268356)
      previous := (0)
      next := (235400)
      square := (9951217268586980893435578189800000000000000)
      linear := (-1068345613499504002880946512017500000000000000)
      constant := (29378765234345591298838054108693244902546150625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree097.table
  base := (65060793125312487121565303310622339121597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-68557363978621602107615949202500000000000000)
      constant := (1899315792467107380896125634538743685219644213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell175.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12213801813215665899/2500000000000000000)
  centralHi := (488552072528626635961/100000000000000000000)
  directionLo := (491090022450967366803/100000000000000000000)
  directionHi := (122772505612741841701/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree098.table
  base := (26817687656931750357776098503345691351361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (536712)
      previous := (0)
      next := (470800)
      square := (19902434537173961786871156379600000000000000)
      linear := (-2157895689963847553833886592514200000000000000)
      constant := (59946832251229098934636901198717224101408660445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree098.table
  base := (67044218893687089186534887004250634570997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3645000000000000000000000000000000000000000
      center := (17226)
      previous := (0)
      next := (14850)
      square := (633630656721103071998824045800000000000000)
      linear := (-69237930239544268370133204659100000000000000)
      constant := (1937762298114537745837180363477198712602256813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell175.Kernel098
