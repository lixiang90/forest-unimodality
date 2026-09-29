import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell186.Parameters
import ForestUnimodality.BinomialMassData.Q427_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q427_792.Batch050_099
import ForestUnimodality.BinomialMassData.Q2567_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2567_4752.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree000.table
  base := (351456448812833725414606077/10000000000000000000000000)
  polynomial :=
    { denominator := 1320000000000000000000000000000000000000000
      center := (5551)
      previous := (0)
      next := (4745)
      square := (220639704171639892127387836800000000000000)
      linear := (-837122252534314790217706554000000000000000)
      constant := (46392251243294051754728002164000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree000.table
  base := (351456448812833725414606077/10000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (33371)
      previous := (0)
      next := (28405)
      square := (1323838225029839352764327020800000000000000)
      linear := (-5022733515205888741306239324000000000000000)
      constant := (278353507459764310528368012984000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree001.table
  base := (111347981501862959429692590506768372026947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-319285174263659168148454801273200000000000000)
      constant := (8883664564125048026612332550353294513888860376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree001.table
  base := (3475757855114492491210493534848243528199/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-5749615333417795975458619536081600000000000000)
      constant := (159737384739648101889540442781238926249999662592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49838185591221999691/100000000000000000000)
  directionHi := (12459546397805499923/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree002.table
  base := (18068615657005940719334618153578844659771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-389945039524626843602250756008400000000000000)
      constant := (6011175786471881302715118092419140208333298272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree002.table
  base := (5770057847140391174601151857443228511263/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-7023975104787145082413379834479200000000000000)
      constant := (108006017369804030746722656541134148749999593400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49838185591221999691/100000000000000000000)
  centralHi := (12459546397805499923/25000000000000000000)
  directionLo := (70481837987173520401/100000000000000000000)
  directionHi := (35240918993586760201/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree003.table
  base := (48058003824229320623697448645189577062571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-51178322753954946561782967860400000000000000)
      constant := (482410559385624841066907911855991595369118552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree003.table
  base := (19168668803574277008431179075900249011363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-922037208461832687707571125875200000000000000)
      constant := (8664920224111006601579713484766858622414750520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70481837987173520401/100000000000000000000)
  centralHi := (35240918993586760201/50000000000000000000)
  directionLo := (17264453920208729763/20000000000000000000)
  directionHi := (5395141850065228051/6250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree004.table
  base := (65317796172030843736470964813302685898141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-531264770046562194509842665478800000000000000)
      constant := (3401660961315244986825219183407318497950719764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree004.table
  base := (65091240504086620272127414975214662776157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-9572694647525843296322900431274400000000000000)
      constant := (61110291537340387092049082731827481510576262504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17264453920208729763/20000000000000000000)
  centralHi := (5395141850065228051/6250000000000000000)
  directionLo := (49838185591221999691/50000000000000000000)
  directionHi := (99676371182443999383/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree005.table
  base := (9026619683233334252055689571387300215429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-601924635307529869963638620214000000000000000)
      constant := (2915814739740682655640648878063338588228392580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree005.table
  base := (22476301381400008129691314176762084619223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-10847054418895192403277660729672000000000000000)
      constant := (52414327672315841404316711396318732554832665712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49838185591221999691/50000000000000000000)
  centralHi := (99676371182443999383/100000000000000000000)
  directionLo := (55720785428611468727/50000000000000000000)
  directionHi := (22288314171444587491/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree006.table
  base := (3145048553966743472677718305071054081959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-74731611174277505046381619438800000000000000)
      constant := (302552434828509240987124191765795115810134040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree006.table
  base := (31308991460090835963659624579686838353179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-1346823798918282390025824558674400000000000000)
      constant := (5443347011142100889149400460359285621596059032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55720785428611468727/50000000000000000000)
  centralHi := (22288314171444587491/20000000000000000000)
  directionLo := (122078124404622668897/100000000000000000000)
  directionHi := (61039062202311334449/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree007.table
  base := (10919293485073229298117423286258210959729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-743244365829465220871230529684400000000000000)
      constant := (2727813030543099298695959703771833804930431432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree007.table
  base := (217279372067267182252053845745822142073/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-13395773961633890617187181326467200000000000000)
      constant := (49121152282391208121807528492970905264093805600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122078124404622668897/100000000000000000000)
  centralHi := (61039062202311334449/50000000000000000000)
  directionLo := (32964861217263998403/25000000000000000000)
  directionHi := (131859444869055993613/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree008.table
  base := (296831623045660258813501750183240547679/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-813904231090432896325026484419600000000000000)
      constant := (2873264062745437148979789950501588121560375800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree008.table
  base := (14754626624260710020714704498656893193729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-14670133733003239724141941624864800000000000000)
      constant := (51780794152257323528843654641665407133805130888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32964861217263998403/25000000000000000000)
  centralHi := (131859444869055993613/100000000000000000000)
  directionLo := (140963675974347040803/100000000000000000000)
  directionHi := (35240918993586760201/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree009.table
  base := (9574202267715449892910348671384487446317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-32761633198200021176993423672400000000000000)
      constant := (115726631441501728768532869408650275772052284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree009.table
  base := (9505297679239987727798711062361798111193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-196845598819414676927119776830400000000000000)
      constant := (695622254175389299656723229596720985144713416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140963675974347040803/100000000000000000000)
  centralHi := (35240918993586760201/25000000000000000000)
  directionLo := (74757278386832999537/50000000000000000000)
  directionHi := (5980582270946639963/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree010.table
  base := (2744011256827174984676175946385921437717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-955223961612368247232618393890000000000000000)
      constant := (3460377425487871480573157417131727328088514536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree010.table
  base := (5432915213643119471479564790713433676691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-17218853275741937938051462221660000000000000000)
      constant := (62428950196207537477780947421987330169497891352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74757278386832999537/50000000000000000000)
  centralHi := (5980582270946639963/4000000000000000000)
  directionLo := (78801090459223471061/50000000000000000000)
  directionHi := (157602180918446942123/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree011.table
  base := (447174342652093972529773773619198979039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-93262166079394174789674031693200000000000000)
      constant := (351538975712236896893333001937994125806474980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree011.table
  base := (2191418593944639078577808111791416483497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-1681201186101026095000565683641600000000000000)
      constant := (6344293788807195761840259811993817950249299544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78801090459223471061/50000000000000000000)
  centralHi := (157602180918446942123/100000000000000000000)
  directionLo := (165294561838180174209/100000000000000000000)
  directionHi := (16529456183818017421/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree012.table
  base := (-407357953167935089237025547065995956189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-121838188014922622015578922595600000000000000)
      constant := (481716427110795848308934297025580521614840716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree012.table
  base := (-443474893449825071637880054727813907183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-2196396979831181794662331424272800000000000000)
      constant := (8695775222128201507692844479752701567165595336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165294561838180174209/100000000000000000000)
  centralHi := (16529456183818017421/10000000000000000000)
  directionLo := (17264453920208729763/10000000000000000000)
  directionHi := (172644539202087297631/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree013.table
  base := (-1295695196898353710877797882106078160973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1167203557395271273594006258095600000000000000)
      constant := (4860064982879808096674602206880226623554429016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree013.table
  base := (-1310447833723099837895871218126813985931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-21041932589849985258915743116852800000000000000)
      constant := (87747949002061334940898951965577854841840198736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17264453920208729763/10000000000000000000)
  centralHi := (172644539202087297631/100000000000000000000)
  directionLo := (89847066812620747149/50000000000000000000)
  directionHi := (179694133625241494299/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree014.table
  base := (-2209199105155124628322231896684845754721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1237863422656238949047802212830800000000000000)
      constant := (5436774574806106950728641888986834614063835832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree014.table
  base := (-2221297368982075842209528677292429568489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-22316292361219334365870503415250400000000000000)
      constant := (98173344846929686278914781951442193283090460784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89847066812620747149/50000000000000000000)
  centralHi := (179694133625241494299/100000000000000000000)
  directionLo := (93238707630403203161/50000000000000000000)
  directionHi := (186477415260806406323/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree015.table
  base := (-1191968064403444413125640616724496746927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-145391476435245180500177574174000000000000000)
      constant := (673641682700386936956115282450240460851929940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree015.table
  base := (-747466368485115579916352883726012456297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-2621183570287631496980584857072000000000000000)
      constant := (12165327747865333042071804390130611522613318592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93238707630403203161/50000000000000000000)
  centralHi := (186477415260806406323/100000000000000000000)
  directionLo := (48255615699999312453/25000000000000000000)
  directionHi := (193022462799997249813/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree016.table
  base := (-1816707290643118962018731080224321021513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1379183153178174299955394122301200000000000000)
      constant := (6736062879522929802928561754745142874690417392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree016.table
  base := (-1820800104116704115319361570819273787423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-24865011903958032579780024012045600000000000000)
      constant := (121655847687358558565761543647020085711526546976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48255615699999312453/25000000000000000000)
  centralHi := (193022462799997249813/100000000000000000000)
  directionLo := (39870548472977599753/20000000000000000000)
  directionHi := (99676371182443999383/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree017.table
  base := (-8376647459821153950356532963206774175161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1449843018439141975409190077036400000000000000)
      constant := (7455176148402008061948050345489841625236988156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree017.table
  base := (-419506338186193098652903359345807854857/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-26139371675327381686734784310443200000000000000)
      constant := (134650841617467293922786379501460326588947021920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39870548472977599753/20000000000000000000)
  centralHi := (99676371182443999383/50000000000000000000)
  directionLo := (102744051690872229333/50000000000000000000)
  directionHi := (205488103381744458667/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree018.table
  base := (-4658470696274228378355422202300251584783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-56314921618522579661592075250800000000000000)
      constant := (304408559635097119029623851836220069397790168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree018.table
  base := (-9328036270071090664059136637379434446399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-338441128971564577699870921096800000000000000)
      constant := (1832759345626646247801067055871350367102971912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102744051690872229333/50000000000000000000)
  centralHi := (205488103381744458667/100000000000000000000)
  directionLo := (42289102792304112241/20000000000000000000)
  directionHi := (105722756980760280603/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree019.table
  base := (-1263560909636999205581979944053636432921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1591162748961077326316781986506800000000000000)
      constant := (9026813250053915804447727793517669898270120928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree019.table
  base := (-2529403155447150220357126889939587832269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-28688091218066079900644304907238400000000000000)
      constant := (163049247923967065452233180050022129700908280928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42289102792304112241/20000000000000000000)
  centralHi := (105722756980760280603/50000000000000000000)
  directionLo := (108619807260780796687/50000000000000000000)
  directionHi := (1737916916172492747/800000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree020.table
  base := (-10767064638844880942848421587765199564497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1661822614222045001770577941242000000000000000)
      constant := (9877903947607847549343036494998253116273459612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree020.table
  base := (-10774562129393576028987354176016314415729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-29962450989435429007599065205636000000000000000)
      constant := (178426980898538170216885329419227215373623685112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108619807260780796687/50000000000000000000)
  centralHi := (1737916916172492747/800000000000000000)
  directionLo := (55720785428611468727/25000000000000000000)
  directionHi := (222883141714445874909/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree021.table
  base := (-11304756466189147844147192820918212698601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-192498053275890297469374877330800000000000000)
      constant := (1196869944592490880889882384338480265484894044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree021.table
  base := (-5655454402231306815739770378769688809517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-3470756751200530901617091722670400000000000000)
      constant := (21619802323463819959706869716119677479646782128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55720785428611468727/25000000000000000000)
  centralHi := (222883141714445874909/100000000000000000000)
  directionLo := (57096814492758071797/25000000000000000000)
  directionHi := (228387257971032287189/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree022.table
  base := (-586543650909734560724143782123594251757/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-163922031340361850243469986428400000000000000)
      constant := (1064384082893746138155772240460130201734761040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree022.table
  base := (-5867957353663025729523146754089855834889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-2955560957470375201955325982039200000000000000)
      constant := (19226948362294387599884688613622455136960401744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57096814492758071797/25000000000000000000)
  centralHi := (228387257971032287189/100000000000000000000)
  directionLo := (116880905569036317191/50000000000000000000)
  directionHi := (233761811138072634383/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree023.table
  base := (-12052621791724521701905681937628103893183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-1873802210004948028131965805447600000000000000)
      constant := (12686807616397198855010535546296127814971653668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree023.table
  base := (-6028373772249413252042869600677260075099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-33785530303543476328463346100828800000000000000)
      constant := (229176556070938013483695000417086078056569476944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116880905569036317191/50000000000000000000)
  centralHi := (233761811138072634383/100000000000000000000)
  directionLo := (239015541523092232763/100000000000000000000)
  directionHi := (59753885380773058191/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree024.table
  base := (-767225121678269490531149914927987151553/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-216051341696212855953973528909200000000000000)
      constant := (1523039789506540408395583398205579007485362112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree024.table
  base := (-2455794683158410734850359180178194388037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-3895543341656980603935345155469600000000000000)
      constant := (27512740591943080023682016530984140672113974520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239015541523092232763/100000000000000000000)
  centralHi := (59753885380773058191/25000000000000000000)
  directionLo := (48831249761849067559/20000000000000000000)
  directionHi := (61039062202311334449/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree025.table
  base := (-12404174443474552839452269419159641998329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2015121940526883379039557714918000000000000000)
      constant := (14769705412244419940938402240766265395097509884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree025.table
  base := (-12406925715281678339808349787817486932069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-36334249846282174542372866697624000000000000000)
      constant := (266807701800023023265736162746021883361673004632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48831249761849067559/20000000000000000000)
  centralHi := (61039062202311334449/25000000000000000000)
  directionLo := (249190927956109998457/100000000000000000000)
  directionHi := (124595463978054999229/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree026.table
  base := (-6220871155509656198991381518962368075939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2085781805787851054493353669653200000000000000)
      constant := (15873716124088169684124051279802298643901774888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree026.table
  base := (-12443984455054866620357700156848974915307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-37608609617651523649327626996021600000000000000)
      constant := (286753280308654347951537048570679870173565478696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249190927956109998457/100000000000000000000)
  centralHi := (124595463978054999229/50000000000000000000)
  directionLo := (63531470212924934579/25000000000000000000)
  directionHi := (254125880851699738317/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree027.table
  base := (-2478192952797908923877979229934416304399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-79868210038845138146190726829200000000000000)
      constant := (630343925527582929361668735112376137630063260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree027.table
  base := (-6196394815515339102057541486608961554179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-480036659123714478472622065363200000000000000)
      constant := (3795673307187425920768377583441650453879985104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63531470212924934579/25000000000000000000)
  centralHi := (254125880851699738317/100000000000000000000)
  directionLo := (51793361760626189289/20000000000000000000)
  directionHi := (129483404401565473223/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree028.table
  base := (-12253921893659031831012649412390381879021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2227101536309786405400945579123600000000000000)
      constant := (18206333459815830804500418547746047468814860716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree028.table
  base := (-76596283149823097212877026112939421043/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-40157329160390221863237147592816800000000000000)
      constant := (328895017970718025066024870078762970059799056640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51793361760626189289/20000000000000000000)
  centralHi := (129483404401565473223/50000000000000000000)
  directionLo := (10548755589524479489/4000000000000000000)
  directionHi := (131859444869055993613/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree029.table
  base := (-6016120997793159362631379034577561219031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2297761401570754080854741533858800000000000000)
      constant := (19434794700102367633208829710468442579938217352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree029.table
  base := (-2406689283964555185358928379805101485819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-41431688931759570970191907891214400000000000000)
      constant := (351088580952129125092915611232094297121495673160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10548755589524479489/4000000000000000000)
  centralHi := (131859444869055993613/50000000000000000000)
  directionLo := (53677368619457327547/20000000000000000000)
  directionHi := (33548355387160829717/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree030.table
  base := (-366475012111076140167079156389741434549/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-263157918536857972923170832066000000000000000)
      constant := (2300513301393998180487096569365021161955345792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree030.table
  base := (-11728177201237813828066313293569721813461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-4745116522569880008571852021068000000000000000)
      constant := (41558814966654020068805601053387785252050149912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53677368619457327547/20000000000000000000)
  centralHi := (33548355387160829717/12500000000000000000)
  directionLo := (10918999389376493177/4000000000000000000)
  directionHi := (136487492367206164713/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree031.table
  base := (-2267959263865591397350159744745043134039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2439081132092689431762333443329200000000000000)
      constant := (22015769322558908502218951321287176644865675220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree031.table
  base := (-567029384820869144132182823359778258513/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-43980408474498269184101428488009600000000000000)
      constant := (397716580564695396454091756249811096135172285280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10918999389376493177/4000000000000000000)
  centralHi := (136487492367206164713/50000000000000000000)
  directionLo := (4335738650670539633/1562500000000000000)
  directionHi := (277487273642914536513/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree032.table
  base := (-1358851619568835512539031328550729537769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2509740997353657107216129398064400000000000000)
      constant := (23368212826915242579761794494954377593610432992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree032.table
  base := (-10871453456693680534604284153108822255697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-45254768245867618291056188786407200000000000000)
      constant := (422149771261697078162682514407390591181177786616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4335738650670539633/1562500000000000000)
  centralHi := (277487273642914536513/100000000000000000000)
  directionLo := (281927351948694081607/100000000000000000000)
  directionHi := (35240918993586760201/12500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree033.table
  base := (-322527007359251233793222382029043924037/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3960000000000000000000000000000000000000000
      center := (16653)
      previous := (0)
      next := (14235)
      square := (661919112514919676382163510400000000000000)
      linear := (-26064655177925502855251771240400000000000000)
      constant := (250120466230882046812484544627527955394603136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree033.table
  base := (-5160691065650174164708214413204534915213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (300339)
      previous := (0)
      next := (255645)
      square := (11914544025268554174878943187200000000000000)
      linear := (-469991192093302700990009586715200000000000000)
      constant := (4518469474644860842912616418243031150248723472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281927351948694081607/100000000000000000000)
  centralHi := (35240918993586760201/12500000000000000000)
  directionLo := (71574644829640924281/25000000000000000000)
  directionHi := (2290388634548509577/800000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree034.table
  base := (-1938086300678504137280401168439803141773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2651060727875592458123721307534800000000000000)
      constant := (26196890441648402648038858311465529788149656540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree034.table
  base := (-2422712471849243359115931849918599836253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-47803487788606316504965709383202400000000000000)
      constant := (473252364731295992114097999418446767265406691936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71574644829640924281/25000000000000000000)
  centralHi := (2290388634548509577/800000000000000000)
  directionLo := (290604062708787670623/100000000000000000000)
  directionHi := (9081376959649614707/3125000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree035.table
  base := (-179597843890491516356387631727725603267/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2721720593136560133577517262270000000000000000)
      constant := (27673090884354795117161991758564812272476026600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree035.table
  base := (-4490114949986547898223015994779403958127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-49077847559975665611920469681600000000000000000)
      constant := (499921168146920165530895890401687181900121207312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290604062708787670623/100000000000000000000)
  centralHi := (9081376959649614707/3125000000000000000)
  directionLo := (294846682202595057457/100000000000000000000)
  directionHi := (147423341101297528729/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree036.table
  base := (-1637908457319694925762255904316399369821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-103421498459167696630789378407600000000000000)
      constant := (1081130217832092720088957664502462940575099540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree036.table
  base := (-8189814651325661507917997408604228249357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-621632189275864379245373209629600000000000000)
      constant := (6510304714075880162363993061542039963491601816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294846682202595057457/100000000000000000000)
  centralHi := (147423341101297528729/50000000000000000000)
  directionLo := (74757278386832999537/25000000000000000000)
  directionHi := (299029113547331998149/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree037.table
  base := (-7319613894027971636202759245089358484323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2863040323658495484485109171740400000000000000)
      constant := (30749156333170050791680844224017916789980601108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree037.table
  base := (-3659916696292412684901931487948379377657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-51626567102714363825829990278395200000000000000)
      constant := (555492744034870856378594176359322807455620058992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74757278386832999537/25000000000000000000)
  centralHi := (299029113547331998149/100000000000000000000)
  directionLo := (151576923946166902421/50000000000000000000)
  directionHi := (303153847892333804843/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree038.table
  base := (-6370289055612475941841864909357403097187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-2933700188919463159938905126475600000000000000)
      constant := (32349005102816345130570102882966452368977880852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree038.table
  base := (-3185232910550528889456548569217151199971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-52900926874083712932784750576792800000000000000)
      constant := (584395227923705154066370774307009988956828128976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151576923946166902421/50000000000000000000)
  centralHi := (303153847892333804843/100000000000000000000)
  directionLo := (307223209141095571349/100000000000000000000)
  directionHi := (6144464182821911427/2000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree039.table
  base := (-1068342108454017644002429401192920824927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-333817783797825648376966786801200000000000000)
      constant := (3776672954801590360026113400548918184433089940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree039.table
  base := (-5341852796154166993460828961582972056949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-6019476293939229115526612319465600000000000000)
      constant := (68226892678466609484624671696683527326958742808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307223209141095571349/100000000000000000000)
  centralHi := (6144464182821911427/2000000000000000000)
  directionLo := (311239369260989278169/100000000000000000000)
  directionHi := (31123936926098927817/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree040.table
  base := (-846798066058068587468293265144146545791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3075019919441398510846497035946000000000000000)
      constant := (35672306414445500211445918735496444394094048180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree040.table
  base := (-846820947131714810681834451438010731981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-55449646416822411146694271173588000000000000000)
      constant := (644433084663523344940235844470914180453707518840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311239369260989278169/100000000000000000000)
  centralHi := (31123936926098927817/10000000000000000000)
  directionLo := (63040872367378776849/20000000000000000000)
  directionHi := (157602180918446942123/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree041.table
  base := (-1523608122578413386232990716505081745357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3145679784702366186300292990681200000000000000)
      constant := (37395751123399647512053545314276869550510048344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree041.table
  base := (-304730819649561651606575504581048120693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-56724006188191760253649031471985600000000000000)
      constant := (675568318514909165565471783428776251105743293040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63040872367378776849/20000000000000000000)
  centralHi := (157602180918446942123/50000000000000000000)
  directionLo := (159560047054415076921/50000000000000000000)
  directionHi := (319120094108830153843/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree042.table
  base := (-890728585690450768761469789541371239819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-357371072218148206861565438379600000000000000)
      constant := (4351154224392041301508319077782615573758696872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree042.table
  base := (-445382757957138168629877899837984406743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-6444262884395678817844865752264800000000000000)
      constant := (78605298642031058270125467524245813274544379424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159560047054415076921/50000000000000000000)
  centralHi := (319120094108830153843/100000000000000000000)
  directionLo := (322988357695836618839/100000000000000000000)
  directionHi := (8074708942395915471/2500000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree043.table
  base := (-436767138114921227836896064547491848703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3286999515224301537207884900151600000000000000)
      constant := (40966214984672783929977194026791380129563447588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree043.table
  base := (-218413216690653314117849931911424607183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-59272725730930458467558552068780800000000000000)
      constant := (740071154917724216570090269833946727349199916048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322988357695836618839/100000000000000000000)
  centralHi := (8074708942395915471/2500000000000000000)
  directionLo := (326810838177192021573/100000000000000000000)
  directionHi := (163405419088596010787/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree044.table
  base := (986811476713995953624472285342739843331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-305241761862297201151061895898800000000000000)
      constant := (3892111850677148129021033408387561524801631684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree044.table
  base := (493381950050611576269774928712111197091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-5504280500209073415864846578834400000000000000)
      constant := (70312608227964230180823585682959278715031563664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326810838177192021573/100000000000000000000)
  centralHi := (163405419088596010787/50000000000000000000)
  directionLo := (165294561838180174209/50000000000000000000)
  directionHi := (330589123676360348419/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree045.table
  base := (248924543348456793725445164348211493663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-126974786879490255115388029986000000000000000)
      constant := (1655608623508510942188167795836336030887986760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree045.table
  base := (1244603639618797132009243665187614744969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-763227719428014280018124353896000000000000000)
      constant := (9969756438024015919309518721862853999316339856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165294561838180174209/50000000000000000000)
  centralHi := (330589123676360348419/100000000000000000000)
  directionLo := (167162356285834406181/50000000000000000000)
  directionHi := (334324712571668812363/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree046.table
  base := (4070508660015584528062818201738976192097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3498979111007204563569272764357200000000000000)
      constant := (46630821394382489825040286278571074822634970788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree046.table
  base := (1017619519291946371898799191371416234113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-63095805045038505788422832963973600000000000000)
      constant := (842405879750582924101748917901924600147035955744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167162356285834406181/50000000000000000000)
  centralHi := (334324712571668812363/100000000000000000000)
  directionLo := (2112618877749416793/625000000000000000)
  directionHi := (338019020439906686881/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree047.table
  base := (1146116141160350439100815955263663643/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3569638976268172239023068719092400000000000000)
      constant := (48601395234665103049539129389659683347300860000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree047.table
  base := (5730556203447859455008487429108878580547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-64370164816407854895377593262371200000000000000)
      constant := (878005501142255681731557535818258445565691762584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2112618877749416793/625000000000000000)
  centralHi := (338019020439906686881/100000000000000000000)
  directionLo := (68334677264820426667/20000000000000000000)
  directionHi := (42709173290512766667/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree048.table
  base := (7469445529644060673536899418503887708457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-404477649058793323830762741536400000000000000)
      constant := (5623683747410941012678575027456602934858038692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree048.table
  base := (3734712953869948269458778291049268761171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-7293836065308578222481372617863200000000000000)
      constant := (101594347171154566881581336807705982130051791536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68334677264820426667/20000000000000000000)
  centralHi := (42709173290512766667/12500000000000000000)
  directionLo := (345289078404174595261/100000000000000000000)
  directionHi := (172644539202087297631/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree049.table
  base := (9287090548758186488855102052251307242579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3710958706790107589930660628562800000000000000)
      constant := (52666096377187111401296928563239060249138067116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree049.table
  base := (9287074842018944442558049447472334224037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-66918884359146553109287113859166400000000000000)
      constant := (951436741231333720572610108491028122036544637864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345289078404174595261/100000000000000000000)
  centralHi := (172644539202087297631/50000000000000000000)
  directionLo := (4360841239231924973/1250000000000000000)
  directionHi := (348867299138553997841/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree050.table
  base := (349484559155041556793406540833626736631/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3781618572051075265384456583298000000000000000)
      constant := (54760222799180383426805561667196428082652215168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree050.table
  base := (11183493325427625837862432950139334216421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-68193244130515902216241874157564000000000000000)
      constant := (989268344383573550472839695283115724255170239912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4360841239231924973/1250000000000000000)
  centralHi := (348867299138553997841/100000000000000000000)
  directionLo := (352409189935867602009/100000000000000000000)
  directionHi := (35240918993586760201/10000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree051.table
  base := (2631736763941034589592239008684198857169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-428030937479115882315361393114800000000000000)
      constant := (6321725854348824549231563860517041851109140820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree051.table
  base := (13158673767985299472136825486199245513257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-7718622655765027924799626050662400000000000000)
      constant := (114204880960119308062316643869603235442203454856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352409189935867602009/100000000000000000000)
  centralHi := (35240918993586760201/10000000000000000000)
  directionLo := (88978958852036858701/25000000000000000000)
  directionHi := (71183167081629486961/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree052.table
  base := (3803154563816030124851357722686555878611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3922938302573010616292048492768400000000000000)
      constant := (59072025808949885708809226978524214946660262576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree052.table
  base := (7606305109411868697440885615434991790341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-70741963673254600430151394754359200000000000000)
      constant := (1067163489804473302682355555130182683053347028304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88978958852036858701/25000000000000000000)
  centralHi := (71183167081629486961/20000000000000000000)
  directionLo := (359388267250482988597/100000000000000000000)
  directionHi := (179694133625241494299/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree053.table
  base := (8672652217435355086695675069493251781323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-3993598167833978291745844447503600000000000000)
      constant := (61289701971813834132037274672323226885669973784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree053.table
  base := (17345298012040147560696211348392818108161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-72016323444623949537106155052756800000000000000)
      constant := (1107227024581175185769094720203628881740022189192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359388267250482988597/100000000000000000000)
  centralHi := (179694133625241494299/50000000000000000000)
  directionLo := (72565493557290622641/20000000000000000000)
  directionHi := (181413733893226556603/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree054.table
  base := (9778369310229252959245297466491331037037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-150528075299812813599986681564400000000000000)
      constant := (2353650408562374431622519277210990825331555448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree054.table
  base := (48891833722684026780822394418803762561/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-904823249580164180790875498162400000000000000)
      constant := (14173265807276980503789683082199447351772572800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72565493557290622641/20000000000000000000)
  centralHi := (181413733893226556603/50000000000000000000)
  directionLo := (366234373213868006693/100000000000000000000)
  directionHi := (183117186606934003347/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree055.table
  base := (21846917879275298304989256831137091073119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-375901627123264876604857850634000000000000000)
      constant := (5986236624735008605058087304463672592584596116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree055.table
  base := (873876551242774744511632747909893452037/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-6778640271578422522819606877232000000000000000)
      constant := (108144182291343957531031976958597262118376940600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366234373213868006693/100000000000000000000)
  centralHi := (183117186606934003347/50000000000000000000)
  directionLo := (73921975316242692477/20000000000000000000)
  directionHi := (184804938290606731193/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree056.table
  base := (12107919955119594767718827021354748286989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4205577763616881318107232311709200000000000000)
      constant := (68189827404305174416278876940609983103686233512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree056.table
  base := (12107918319134309998029174141721001708711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-75839402758731996857970435947949600000000000000)
      constant := (1231881447439627729065259673779039885435579017584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73921975316242692477/20000000000000000000)
  centralHi := (184804938290606731193/50000000000000000000)
  directionLo := (74590966104322562529/20000000000000000000)
  directionHi := (186477415260806406323/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree057.table
  base := (13331751453870656274515729218792450156053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-475137514319760999284558696271600000000000000)
      constant := (7841359395228584323497333042134719825759533736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree057.table
  base := (26663500296262499827223723217299824690461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-8568195836677927329436132916260800000000000000)
      constant := (141657872872097119652419404208072469654329666088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74590966104322562529/20000000000000000000)
  centralHi := (186477415260806406323/50000000000000000000)
  directionLo := (18813502488401118033/5000000000000000000)
  directionHi := (376270049768022360661/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree058.table
  base := (29189905454819479353212439149872234200849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4346897494138816669014824221179600000000000000)
      constant := (72995824274790762523170068782041491069610084196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree058.table
  base := (29189903371144637447474236412695593324997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-78388122301470695071879956544744800000000000000)
      constant := (1318704229455938599865350958190173924732837282984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18813502488401118033/5000000000000000000)
  centralHi := (376270049768022360661/100000000000000000000)
  directionLo := (379556313470682650809/100000000000000000000)
  directionHi := (37955631347068265081/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree059.table
  base := (15897523219684343102801899452755102034861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4417557359399784344468620175914800000000000000)
      constant := (75460596513906720684644951188764722040349381288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree059.table
  base := (31795044777317927628060458114652157203013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-79662482072840044178834716843142400000000000000)
      constant := (1363231567494745817605006567137550742077764589736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379556313470682650809/100000000000000000000)
  centralHi := (37955631347068265081/10000000000000000000)
  directionLo := (382814367335501398933/100000000000000000000)
  directionHi := (191407183667750699467/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree060.table
  base := (34478924988420419173876540453695755150511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-498690802740083557769157347850000000000000000)
      constant := (8662950137797919530633068732351298709435625916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree060.table
  base := (34478923663060445237759574741164181477657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-8992982427134377031754386349060000000000000000)
      constant := (156500318818251046193282355489860201141300130056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382814367335501398933/100000000000000000000)
  centralHi := (191407183667750699467/50000000000000000000)
  directionLo := (48255615699999312453/12500000000000000000)
  directionHi := (3088359404799955997/800000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree061.table
  base := (18620770208297058108382642813146269636671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4558877089921719695376212085385200000000000000)
      constant := (80513688426744768242062303103528772709672099768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree061.table
  base := (581899052500205718803191463365156753507/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-82211201615578742392744237439937600000000000000)
      constant := (1454518134592837144892060317047227706379890669056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48255615699999312453/12500000000000000000)
  centralHi := (3088359404799955997/800000000000000000)
  directionLo := (77849734572323463181/20000000000000000000)
  directionHi := (194624336430808657953/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree062.table
  base := (20041446092832244832124271467565594285847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4629536955182687370830008040120400000000000000)
      constant := (83102008052496613905923482173563783116764691576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree062.table
  base := (20041445671790664154357383397731144385413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-83485561386948091499698997738335200000000000000)
      constant := (1501277362810287170443280571792176664241486325072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77849734572323463181/20000000000000000000)
  centralHi := (194624336430808657953/50000000000000000000)
  directionLo := (392426265771744010643/100000000000000000000)
  directionHi := (98106566442936002661/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree063.table
  base := (43002979872847529561413992859851593625257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-174081363720135372084585333142800000000000000)
      constant := (3175241114846740312629954563955204513943873164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree063.table
  base := (43002979201891273556244213361477835978643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-1046418779732314081563626642428800000000000000)
      constant := (19120747576863725728190424867435519907045937816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392426265771744010643/100000000000000000000)
  centralHi := (98106566442936002661/25000000000000000000)
  directionLo := (197789167303583990419/50000000000000000000)
  directionHi := (395578334607167980839/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree064.table
  base := (9200360629184995854769164535664387320401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4770856685704622721737599949590800000000000000)
      constant := (88402194558816607314222538741250533202545004020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree064.table
  base := (46001802611454151595625822986563859777983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-86034280929686789713608518335130400000000000000)
      constant := (1597027707111583961649182224879211292057248819576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197789167303583990419/50000000000000000000)
  centralHi := (395578334607167980839/100000000000000000000)
  directionLo := (398705484729775997531/100000000000000000000)
  directionHi := (99676371182443999383/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree065.table
  base := (49079361743732555752304866004402845377083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4841516550965590397191395904326000000000000000)
      constant := (91114061416121785972902406437941609150163161932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree065.table
  base := (49079361318087322975363711825624129647077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-87308640701056138820563278633528000000000000000)
      constant := (1646018822787784131893538000298242455816312120744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398705484729775997531/100000000000000000000)
  centralHi := (99676371182443999383/25000000000000000000)
  directionLo := (401808297943970700783/100000000000000000000)
  directionHi := (25113018621498168799/6250000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree066.table
  base := (5223565546085522210784098447959889973217/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3960000000000000000000000000000000000000000
      center := (16653)
      previous := (0)
      next := (14235)
      square := (661919112514919676382163510400000000000000)
      linear := (-49617943598248061339850422818800000000000000)
      constant := (948152632977014477887413889824821164293939320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree066.table
  base := (26117827560978711427723764684442101085283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (300339)
      previous := (0)
      next := (255645)
      square := (11914544025268554174878943187200000000000000)
      linear := (-894777782549752403308263019514400000000000000)
      constant := (17128827278924701863465777337923606593071794448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401808297943970700783/100000000000000000000)
  centralHi := (25113018621498168799/6250000000000000000)
  directionLo := (50610916720057760157/12500000000000000000)
  directionHi := (404887333760462081257/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree067.table
  base := (55470684135622268305345018179795542079019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-4982836281487525748098987813796400000000000000)
      constant := (96661342298286410811860825199732604431665860876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree067.table
  base := (55470683865854522820411450273869693722057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-89857360243794837034472799230323200000000000000)
      constant := (1746232940477929374813105493446720499508231407304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50610916720057760157/12500000000000000000)
  centralHi := (404887333760462081257/100000000000000000000)
  directionLo := (101985782643550647993/25000000000000000000)
  directionHi := (407943130574202591973/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree068.table
  base := (58784447640690608353695464395972311851931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5053496146748493423552783768531600000000000000)
      constant := (99496756311815360132727029366963098513843102924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree068.table
  base := (14696111856499814240259157001995935423859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-91131720015164186141427559528720800000000000000)
      constant := (1797455942293588170183628329404742102969701712992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101985782643550647993/25000000000000000000)
  centralHi := (407943130574202591973/100000000000000000000)
  directionLo := (102744051690872229333/25000000000000000000)
  directionHi := (410976206763488917333/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree069.table
  base := (12435389175131632177592587811734273759879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-569350668001051233222953302585200000000000000)
      constant := (11374816966819457563957988446809972482490164620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree069.table
  base := (3108847285241781431347310543997005303993/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-10267342198503726138709146647457600000000000000)
      constant := (205491433999075481702935081182423168837509662880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102744051690872229333/25000000000000000000)
  centralHi := (410976206763488917333/100000000000000000000)
  directionLo := (206993530858292212633/50000000000000000000)
  directionHi := (413987061716584425267/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree070.table
  base := (65648178761269544035324816517258514606391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5194815877270428774460375678002000000000000000)
      constant := (105291131463858556649603286946705102806628952764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree070.table
  base := (65648178625380468816184897435360611424777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-93680439557902884355337080125516000000000000000)
      constant := (1902133831517878003405519895670005793385345235144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206993530858292212633/50000000000000000000)
  centralHi := (413987061716584425267/100000000000000000000)
  directionLo := (83395235358323959827/20000000000000000000)
  directionHi := (13030505524738118723/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree071.table
  base := (34599073117435361027295985691174901091751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5265475742531396449914171632737200000000000000)
      constant := (108250092596809387037473623671443741644802012408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree071.table
  base := (34599073063396609738947666843050631239723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-94954799329272233462291840423913600000000000000)
      constant := (1955588718829250696140076213785812375096395617712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83395235358323959827/20000000000000000000)
  centralHi := (13030505524738118723/3125000000000000000)
  directionLo := (419944016214996517657/100000000000000000000)
  directionHi := (209972008107498258829/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree072.table
  base := (72826848246843288372772796559633486969973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-197634652140457930569183984721200000000000000)
      constant := (4120379114751198860294271971517787823080400796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree072.table
  base := (36413424080451193187481762110527665620359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-1188014309884463982336377786695200000000000000)
      constant := (24812192196195112825293728118759034045769135216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419944016214996517657/100000000000000000000)
  centralHi := (209972008107498258829/50000000000000000000)
  directionLo := (42289102792304112241/10000000000000000000)
  directionHi := (422891027923041122411/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree073.table
  base := (38267142378903573999048967312615570348357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5406795473053331800821763542207600000000000000)
      constant := (114291561966733645976961119736868961639873975656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree073.table
  base := (76534284689481974853560124111987381750497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-97503518872010931676201361020708800000000000000)
      constant := (2064730378678563317432310125676816184654636718984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42289102792304112241/10000000000000000000)
  centralHi := (422891027923041122411/100000000000000000000)
  directionLo := (85163528870246196353/20000000000000000000)
  directionHi := (212908822175615490883/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree074.table
  base := (80320455736425915663846421192982496875211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5477455338314299476275559496942800000000000000)
      constant := (117374070200934705636524424501314785807495772044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree074.table
  base := (3212818227284635236529826133418308656591/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-98777878643380280783156121319106400000000000000)
      constant := (2120417151168064438948432529210714917657847103800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85163528870246196353/20000000000000000000)
  centralHi := (212908822175615490883/50000000000000000000)
  directionLo := (428724283174928782313/100000000000000000000)
  directionHi := (214362141587464391157/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree075.table
  base := (84185361157685075563093975346348452561193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-616457244841696350192150605742000000000000000)
      constant := (13388640088878319903215622001696193859356556708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree075.table
  base := (2104634027863080480514227206012139221001/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-11116915379416625543345653513056000000000000000)
      constant := (241871987260352573609125793051038117481609856320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428724283174928782313/100000000000000000000)
  centralHi := (214362141587464391157/50000000000000000000)
  directionLo := (107902837001304561019/25000000000000000000)
  directionHi := (431611348005218244077/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree076.table
  base := (88129001001540972765401413433291091081621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5618775068836234827183151406413200000000000000)
      constant := (123662633762858375006316702522827343934763869684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree076.table
  base := (17625800193449002855354746513430046735771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-101326598186118978997065641915901600000000000000)
      constant := (2234022581190157833875250315059569839700624965560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107902837001304561019/25000000000000000000)
  centralHi := (431611348005218244077/100000000000000000000)
  directionLo := (108619807260780796687/25000000000000000000)
  directionHi := (434479229043123186749/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree077.table
  base := (46075687625930343532094816064557833472061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-517221357645200227512449760104400000000000000)
      constant := (11533517189923883478624910077932568236988850808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree077.table
  base := (46075687612307097700991657932865820443807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-9327359814317120736729127474027200000000000000)
      constant := (208358294427087512729725219499145491226222213328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108619807260780796687/25000000000000000000)
  centralHi := (434479229043123186749/100000000000000000000)
  directionLo := (109332075923803059781/25000000000000000000)
  directionHi := (3498626429561697913/800000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree078.table
  base := (1503945060868595006720824765580266110209/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-640010533262018908676749257320400000000000000)
      constant := (14457325197589570497478981392761628907268505856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree078.table
  base := (96252483873947701904175149409010460610069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-11541701969873075245663906945855200000000000000)
      constant := (261178206428626388903628044550324492195514290152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109332075923803059781/25000000000000000000)
  centralHi := (3498626429561697913/800000000000000000)
  directionLo := (220079468576669411193/50000000000000000000)
  directionHi := (440158937153338822387/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree079.table
  base := (100432326922100831707005800773683255541789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5830754664619137853544539270618800000000000000)
      constant := (133404346829871950941018519861795578350260295956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree079.table
  base := (100432326904912726254190419598044977418043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-105149677500227026317929922811094400000000000000)
      constant := (2410010438661890841237558716136537520304545239896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220079468576669411193/50000000000000000000)
  centralHi := (440158937153338822387/100000000000000000000)
  directionLo := (221485741470518798773/50000000000000000000)
  directionHi := (442971482941037597547/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree080.table
  base := (52345452161338939243914417419533509421177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-5901414529880105528998335225354000000000000000)
      constant := (136733949243518502349393835009610783406695646216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree080.table
  base := (20938180861805897546199629060350164826199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-106424037271596375424884683109492000000000000000)
      constant := (2470160981104738719520724985524717107566167503640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221485741470518798773/50000000000000000000)
  centralHi := (442971482941037597547/100000000000000000000)
  directionLo := (445766283428891749817/100000000000000000000)
  directionHi := (222883141714445874909/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree081.table
  base := (10902821609011700514077772843421529837301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-221187940560780489053782636299600000000000000)
      constant := (5189064222924568690103953468826280613237610520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree081.table
  base := (5451410803964052706378715525178066466759/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-1329609840036613883109128930961600000000000000)
      constant := (31247598582484314597503162440580451301168088160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445766283428891749817/100000000000000000000)
  centralHi := (222883141714445874909/50000000000000000000)
  directionLo := (448543670320997997223/100000000000000000000)
  directionHi := (56067958790124749653/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree082.table
  base := (56722131109204420490483983301771644324483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6042734260402040879905927134824400000000000000)
      constant := (143516701155970916422927033283573211088194063064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree082.table
  base := (2836106555245177465655497109182593472813/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-108972756814335073638794203706287200000000000000)
      constant := (2592693950887227661322552922135212164045875813440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448543670320997997223/100000000000000000000)
  centralHi := (56067958790124749653/12500000000000000000)
  directionLo := (451303965114486034603/100000000000000000000)
  directionHi := (112825991278621508651/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree083.table
  base := (2358780854049813009884324593408772020161/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6113394125663008555359723089559600000000000000)
      constant := (146969850654342708236656661020799774913919592200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree083.table
  base := (117939042695663472209551453939284759158039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-110247116585704422745748964004684800000000000000)
      constant := (2655076378219244308769720291083445279564571697208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451303965114486034603/100000000000000000000)
  centralHi := (112825991278621508651/25000000000000000000)
  directionLo := (454047479533894468091/100000000000000000000)
  directionHi := (113511869883473617023/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree084.table
  base := (119641169470753234145599661205155690003/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-687117110102664025645946560477200000000000000)
      constant := (16718242501545524094491463260594089982108741632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree084.table
  base := (15314069691579173293456770187479626852479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-12391275150785974650300413811453600000000000000)
      constant := (302022529686033750571530687450551420657993387456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454047479533894468091/100000000000000000000)
  centralHi := (113511869883473617023/25000000000000000000)
  directionLo := (57096814492758071797/12500000000000000000)
  directionHi := (456774515942064574377/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree085.table
  base := (127164806721378027854928900088707607494649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6254713856184943906267314999030000000000000000)
      constant := (153999696734526385773042840127417693044220219396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree085.table
  base := (25432961343415813862777787465070576383313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-112795836128443120959658484601480000000000000000)
      constant := (2782073117749838926794839764439767043887826256680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57096814492758071797/12500000000000000000)
  centralHi := (456774515942064574377/100000000000000000000)
  directionLo := (18379414709163401089/4000000000000000000)
  directionHi := (229742683864542513613/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree086.table
  base := (65947895124617892748971811362934855366019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6325373721445911581721110953765200000000000000)
      constant := (157576393316065889544444146057273096139538817752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree086.table
  base := (26379158049165033016017742105346068034177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-114070195899812470066613244899877600000000000000)
      constant := (2846687429943609063883802309989403652609068759720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18379414709163401089/4000000000000000000)
  centralHi := (229742683864542513613/50000000000000000000)
  directionLo := (231090159840351910803/50000000000000000000)
  directionHi := (462180319680703821607/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree087.table
  base := (136705508118772512558158751336071680165031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-710670398522986584130545212055600000000000000)
      constant := (17910474695379601725400905334086028238798875036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree087.table
  base := (34176377029016757396719208551055456506429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-12816061741242424352618667244252800000000000000)
      constant := (323560633750403889736443931836981549935024340128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231090159840351910803/50000000000000000000)
  centralHi := (462180319680703821607/100000000000000000000)
  directionLo := (232429824163758440659/50000000000000000000)
  directionHi := (464859648327516881319/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree088.table
  base := (35398490081861101265402359994371324260199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5957272012634277087439471593600000000000000)
      linear := (-587881222906167902966245714839600000000000000)
      constant := (14986666687407112403139957105056157598653396944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree088.table
  base := (141593960325298557581653295554968043987481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2703051)
      previous := (0)
      next := (2300805)
      square := (107230896227416987573910488684800000000000000)
      linear := (-10601719585686469843683887772424800000000000000)
      constant := (270740721743468024520146021621403509957884881112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232429824163758440659/50000000000000000000)
  centralHi := (464859648327516881319/100000000000000000000)
  directionLo := (116880905569036317191/25000000000000000000)
  directionHi := (93504724455229053753/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree089.table
  base := (36640286718239271591550621364677639161491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6537353317228814608082498817970800000000000000)
      constant := (168553577225161403520361664565887888662748372656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree089.table
  base := (146561146871255332203849815867148873297527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-117893275213920517387477525795070400000000000000)
      constant := (3044994136215550914589803925522090104717612473144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116880905569036317191/25000000000000000000)
  centralHi := (93504724455229053753/20000000000000000000)
  directionLo := (235086251261761820583/50000000000000000000)
  directionHi := (470172502523523641167/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree090.table
  base := (18950883469152399475939756976965271521691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2427036745888038813401266204800000000000000)
      linear := (-244741228981103047538381287878000000000000000)
      constant := (6381296416643849151206912672046928593995962656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree090.table
  base := (151607067751869798089658215075511461831631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (367081)
      previous := (0)
      next := (312455)
      square := (14562220475328232880407597228800000000000000)
      linear := (-1471205370188763783881880075228000000000000000)
      constant := (38426966603263999090171595105552855855477169272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235086251261761820583/50000000000000000000)
  centralHi := (470172502523523641167/100000000000000000000)
  directionLo := (1846900557638050103/390625000000000000)
  directionHi := (472806542755340826369/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree091.table
  base := (9795732685394108586174175046214349347511/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6678673047750749958990090727441200000000000000)
      constant := (176077611634070339577765075284237697629117139904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree091.table
  base := (39182930741308967767316817716493901048723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-120441994756659215601387046391865600000000000000)
      constant := (3180918415123302234635613047045690661563417827424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1846900557638050103/390625000000000000)
  centralHi := (472806542755340826369/100000000000000000000)
  directionLo := (29714124351849901027/6250000000000000000)
  directionHi := (475425989629598416433/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree092.table
  base := (161935112510429094132160652970032034691791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6749332913011717634443886682176400000000000000)
      constant := (179901402379150559271073528353946535888056974364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree092.table
  base := (40483778127395238987763505925312047323341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-121716354528028564708341806690263200000000000000)
      constant := (3249996496991054968790882498907217412235026760608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29714124351849901027/6250000000000000000)
  centralHi := (475425989629598416433/100000000000000000000)
  directionLo := (478031083046184465527/100000000000000000000)
  directionHi := (59753885380773058191/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree093.table
  base := (167217236383916065117805134307011508239127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-757776975363631701099742515212400000000000000)
      constant := (20418486164950998888052743385668942129889637212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree093.table
  base := (10451077273952736354826646963699074329207/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-13665634922155323757255174109851200000000000000)
      constant := (368868726718496646255534808522661897320071399296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478031083046184465527/100000000000000000000)
  centralHi := (59753885380773058191/12500000000000000000)
  directionLo := (15019439262603005063/3125000000000000000)
  directionHi := (480622056403296162017/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree094.table
  base := (43144523646297408886707471192755683581439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6890652643533652985351478591646800000000000000)
      constant := (187672530950233806454184903962829275276506938224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree094.table
  base := (172578094584656806358074665672329890080779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-124265074070767262922251327287058400000000000000)
      constant := (3390384545548440606742010235807583178193083478488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15019439262603005063/3125000000000000000)
  centralHi := (480622056403296162017/100000000000000000000)
  directionLo := (24159956842074360659/5000000000000000000)
  directionHi := (483199136841487213181/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree095.table
  base := (890088435563772342233575961964815028047/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-6961312508794620660805274546382000000000000000)
      constant := (191619868776116385465533506041336221671910917600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree095.table
  base := (89008843556166106889735891235085973754159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-125539433842136612029206087585456000000000000000)
      constant := (3461694512235917429874017818037144303542089779696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24159956842074360659/5000000000000000000)
  centralHi := (483199136841487213181/100000000000000000000)
  directionLo := (485762545476062175967/100000000000000000000)
  directionHi := (15180079546126942999/3125000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree096.table
  base := (183536013965185323823854678535355928440473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7281110237664116440203798614400000000000000)
      linear := (-781330263783954259584341166790800000000000000)
      constant := (21734265440238983546423461359826410424286700388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree096.table
  base := (91768006982425366973954354526996552330497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3303729)
      previous := (0)
      next := (2812095)
      square := (131059984277954095923668375059200000000000000)
      linear := (-14090421512611773459573427542650400000000000000)
      constant := (392638715614210971844552949494956691350259217552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485762545476062175967/100000000000000000000)
  centralHi := (15180079546126942999/3125000000000000000)
  directionLo := (488312497618490675591/100000000000000000000)
  directionHi := (61039062202311334449/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree097.table
  base := (189133075141117782159780084705454670231931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-7102632239316556011712866455852400000000000000)
      constant := (199638091508283715108215812948184044891772622924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree097.table
  base := (189133075140852685645609886076104560795829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-128088153384875310243115608182251200000000000000)
      constant := (3606546330423425067958576303543978682625914242088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell186.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488312497618490675591/100000000000000000000)
  centralHi := (61039062202311334449/12500000000000000000)
  directionLo := (61356150373433625457/12500000000000000000)
  directionHi := (490849202987469003657/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree098.table
  base := (194808870639240783065761993470901791325061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (65529992138977047961834187529600000000000000)
      linear := (-7173292104577523687166662410587600000000000000)
      constant := (203708976414463576225267740089557133827107691444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2567
  qDenominator := 4752
  table := BinomialMassData.Q2567_4752.Degree098.table
  base := (97404435319515384329245431770976765949119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29733561)
      previous := (0)
      next := (25308855)
      square := (1179539858501586863313015375532800000000000000)
      linear := (-129362513156244659350070368480648800000000000000)
      constant := (3680088181921573868790143690308693632761693405936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2567_4752.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell186.Kernel098
