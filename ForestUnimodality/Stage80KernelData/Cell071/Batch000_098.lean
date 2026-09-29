import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell071.Parameters
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch000_049
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch050_099
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree000.table
  base := (22432248059769408458219431/625000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (275157810296115072634659525000000000000)
      linear := (4125049373751582407546245500000000000)
      constant := (89728992239077633832877724000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree000.table
  base := (22432248059769408458219431/625000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (275157810296115072634659525000000000000)
      linear := (4125049373751582407546245500000000000)
      constant := (89728992239077633832877724000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree001.table
  base := (26493253624785294502765016996558603667627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-2093074302605588478334003691545276500000000000)
      constant := (416137033399295958821245931741608102190623838018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree001.table
  base := (105780605749828399447773835705003740582691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-466363539965821934275473721598742000000000000)
      constant := (92307800028057728563015528184416307778471916033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24997091050574339969/50000000000000000000)
  directionHi := (49994182101148679939/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree002.table
  base := (32053036655787861601461923280597447780437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-4218505768877192410428821438391001500000000000)
      constant := (253487312400678125005127614397799345918749117279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree002.table
  base := (31943455129564467992967887975843586916551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-469958780373156984693341949965458500000000000)
      constant := (28070959121602954709893968625729493643749939213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/50000000000000000000)
  centralHi := (49994182101148679939/100000000000000000000)
  directionLo := (70702450367194700757/100000000000000000000)
  directionHi := (35351225183597350379/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree003.table
  base := (79889252779105416963223801275749614047341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-2819527660066131707788284082327434000000000000)
      constant := (71700283328640339036888913442781462867942663983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree003.table
  base := (79509723774532367207712957532778147279051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-942314387684537336331929385508728000000000000)
      constant := (23793470736918272513476724015025292875657175571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702450367194700757/100000000000000000000)
  centralHi := (35351225183597350379/50000000000000000000)
  directionLo := (86592463482040081719/100000000000000000000)
  directionHi := (2164811587051002043/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree004.table
  base := (6432954097214894398974306237224203591051/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-8469368701420400274618456932082451500000000000)
      constant := (109229354306861195566916523523654574979689288834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree004.table
  base := (51165572123987901948201111156974466507411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-3774051204614596079218208513190534000000000000)
      constant := (48306025438723238724766809857751922952598653393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86592463482040081719/100000000000000000000)
  centralHi := (2164811587051002043/2500000000000000000)
  directionLo := (24997091050574339969/25000000000000000000)
  directionHi := (99988364202297359877/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree005.table
  base := (34284504598508896795152789215828954155473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-42379200670768016826853098715712706000000000000)
      constant := (320936537640687673274284888044015056935458628691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree005.table
  base := (1362343541104914073836064542783145343599/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-4721159246175580149440628869854884000000000000)
      constant := (35493088965873709671462820665431863877579380925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/25000000000000000000)
  centralHi := (99988364202297359877/100000000000000000000)
  directionLo := (111790389657671715219/100000000000000000000)
  directionHi := (5589519482883585761/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree006.table
  base := (23511188951741678262453503791423696113569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-5653436281761603617248041078121734000000000000)
      constant := (28821033169257105162692302433114364855830538347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree006.table
  base := (23340198873588008218369235393605893511169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-1889422429245521406554349742173078000000000000)
      constant := (9571921664520199504540064338874245788758329049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111790389657671715219/100000000000000000000)
  centralHi := (5589519482883585761/5000000000000000000)
  directionLo := (7653764765974877899/6250000000000000000)
  directionHi := (24492047251119609277/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree007.table
  base := (8218672795998465038827107344885835533467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (5762988)
      previous := (2881494)
      next := (2881494)
      square := (88096175491265978345148401481150000000000000)
      linear := (-605945432662661717179710619290597000000000000)
      constant := (2357622302708655218117444902578088209703997761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree007.table
  base := (4076287404761098372873845047022903354913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44467500000000000000000000000000000000000000
      center := (320166)
      previous := (160083)
      next := (160083)
      square := (4894231971736998796952688971175000000000000)
      linear := (-33751914945395654540231987669304000000000000)
      constant := (130695176674625191019469980976775944473837531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/6250000000000000000)
  centralHi := (24492047251119609277/20000000000000000000)
  directionLo := (26454434567943201659/20000000000000000000)
  directionHi := (16534021604964501037/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree008.table
  base := (5771786509962208753923096387542049764703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-33942189133013632005995455838930703000000000000)
      constant := (111995655953143385148729173740952927671664567101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree008.table
  base := (11437665070275684232441504323067185680939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-7562483370858532360107889939847934000000000000)
      constant := (24873463858929046449955530828141577553636237657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26454434567943201659/20000000000000000000)
  centralHi := (16534021604964501037/12500000000000000000)
  directionLo := (28280980146877880303/20000000000000000000)
  directionHi := (35351225183597350379/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree009.table
  base := (7972494932194303847702092128550265304113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-2829114967819025175569266024638678000000000000)
      constant := (8573961484381409667201111283943003626416212873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree009.table
  base := (985505516433086147873511318412131845709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-709132617701626369194192524709357000000000000)
      constant := (2145278199791200573287571631055383349394448778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28280980146877880303/20000000000000000000)
  centralHi := (35351225183597350379/25000000000000000000)
  directionLo := (74991273151723019907/50000000000000000000)
  directionHi := (29996509260689207963/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree010.table
  base := (5236536536800004396146564767392752887531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-84887829996200095468749453652627206000000000000)
      constant := (249739360845471368690014570381097478964236628577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree010.table
  base := (5159659778083506136441540380576950212293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-9456699453980500500552730653176634000000000000)
      constant := (27803495260544006697329609732814878457876723959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991273151723019907/50000000000000000000)
  centralHi := (29996509260689207963/20000000000000000000)
  directionLo := (39523871299213079473/25000000000000000000)
  directionHi := (158095485196852317893/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree011.table
  base := (763764312795347467890952512355898956029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162067500000000000000000000000000000000000000
      center := (1166886)
      previous := (583443)
      next := (583443)
      square := (17837655368066251813687073027175000000000000)
      linear := (-192953627812575436357703976528946500000000000)
      constant := (571316427015053734939164950681507361622491983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree011.table
  base := (93312420952412037601397619231979025757/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 18007500000000000000000000000000000000000000
      center := (129654)
      previous := (64827)
      next := (64827)
      square := (1981961707562916868187452558575000000000000)
      linear := (-21495470032110505311518907045126000000000000)
      constant := (63659486529654047134296901669173621880221368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39523871299213079473/25000000000000000000)
  centralHi := (158095485196852317893/100000000000000000000)
  directionLo := (165811943730211924133/100000000000000000000)
  directionHi := (82905971865105962067/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree012.table
  base := (15794391218578690959013681794373735909/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-2830313381288136859041888767427583500000000000)
      constant := (8626109311788402215075150730169022127801115340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree012.table
  base := (74999428918527280311573768987281278317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-945909628091872386749797613875444500000000000)
      constant := (2885358705270455189560922687102412277031732628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165811943730211924133/100000000000000000000)
  centralHi := (82905971865105962067/50000000000000000000)
  directionLo := (173184926964080163439/100000000000000000000)
  directionHi := (2164811587051002043/1250000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree013.table
  base := (-59251322058585004520830172094259344717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-27598251897864835663471816653693976500000000000)
      constant := (87757740971234692155005177650613981384663755961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree013.table
  base := (-29645202480374185180638125254038949823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-6149011789331726355609995861584842000000000000)
      constant := (19578670434627268324769864743704506878877083255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173184926964080163439/100000000000000000000)
  centralHi := (2164811587051002043/1250000000000000000)
  directionLo := (22532073380071945891/12500000000000000000)
  directionHi := (180256587040575567129/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree014.table
  base := (-1508441664490914900452615378460681816771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (11525976)
      previous := (5762988)
      next := (5762988)
      square := (176192350982531956690296802962300000000000000)
      linear := (-2426423131766239966985031379635894000000000000)
      constant := (8112351930511136434110548527495944672725848007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree014.table
  base := (-195572323419858147675381518372253569469/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44467500000000000000000000000000000000000000
      center := (320166)
      previous := (160083)
      next := (160083)
      square := (4894231971736998796952688971175000000000000)
      linear := (-67577202144002228476747000407316500000000000)
      constant := (226310814973260072200398438099381451519709794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22532073380071945891/12500000000000000000)
  centralHi := (180256587040575567129/100000000000000000000)
  directionLo := (9353055037724226197/5000000000000000000)
  directionHi := (187061100754484523941/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree015.table
  base := (-2591216203751441280527815722543430549287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-14155162146848019345627312065504634000000000000)
      constant := (49960602130039243212994415454630890040171774419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree015.table
  base := (-2644496430328594596196433549235161020649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-4730746553928473617221610812166128000000000000)
      constant := (16729361584969564159759354765051540535120031871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9353055037724226197/5000000000000000000)
  centralHi := (187061100754484523941/100000000000000000000)
  directionLo := (96813317342504881199/50000000000000000000)
  directionHi := (193626634685009762399/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree016.table
  base := (-1756646575750803788146158207842091718481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-67949092593359294919512539788462303000000000000)
      constant := (253616067097833546032416770730049755140089897773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree016.table
  base := (-712793252162742718956283634763938812939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-15139347703346404921887252793162734000000000000)
      constant := (56626640724540811465153780291501929981892231715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96813317342504881199/50000000000000000000)
  centralHi := (193626634685009762399/100000000000000000000)
  directionLo := (24997091050574339969/12500000000000000000)
  directionHi := (199976728404594719753/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree017.table
  base := (-4295144146465481151951290424566274458483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-144399911051805005567404350564307506000000000000)
      constant := (570104808765236015797729506455312949207270629639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree017.table
  base := (-868669460335199612476355262182266920277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-16086455744907388992109673149827084000000000000)
      constant := (63654843298300253133051956951100793730813085245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/12500000000000000000)
  centralHi := (199976728404594719753/100000000000000000000)
  directionLo := (103065646734699937609/50000000000000000000)
  directionHi := (206131293469399875219/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree018.table
  base := (-4952586060183283139088354088829959672577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-5663023589514497085029023020432978000000000000)
      constant := (23634791639961780457951108570625385285963257383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree018.table
  base := (-2499199401097141008686266194481356583657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-2838927297744728843722015584415239000000000000)
      constant := (11876492882934634844902600476335958803959384703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103065646734699937609/50000000000000000000)
  centralHi := (206131293469399875219/100000000000000000000)
  directionLo := (1657088680481125799/781250000000000000)
  directionHi := (212107351101584102273/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree019.table
  base := (-549840877689929906602456230267409457247/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-80701681390988918512081446269536653000000000000)
      constant := (355617753013964420857202032107021568504604482255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree019.table
  base := (-5541884910717187316667776170399168350991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-17980671828029357132554513863155784000000000000)
      constant := (79427857963036309362767103196638091884505231067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1657088680481125799/781250000000000000)
  centralHi := (212107351101584102273/100000000000000000000)
  directionLo := (43583917508775406419/20000000000000000000)
  directionHi := (6809987110746157253/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree020.table
  base := (-2971662231002926656106000435714934633941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-84952544323532126376271081763228103000000000000)
      constant := (394654588534532925064373160265009669830746321953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree020.table
  base := (-1196901965779111235021721470151483244487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-18927779869590341202776934219820134000000000000)
      constant := (88152215908482341019812904593026744044925884095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43583917508775406419/20000000000000000000)
  centralHi := (6809987110746157253/3125000000000000000)
  directionLo := (223580779315343430439/100000000000000000000)
  directionHi := (5589519482883585761/2500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree021.table
  base := (-157413369467663534463525007669879102211/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44467500000000000000000000000000000000000000
      center := (320166)
      previous := (160083)
      next := (160083)
      square := (4894231971736998796952688971175000000000000)
      linear := (-101137649950198791655851153352516500000000000)
      constant := (494494449512300827583800673565142604089729430) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree021.table
  base := (-791934565822582812866790811318867479543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14822500000000000000000000000000000000000000
      center := (106722)
      previous := (53361)
      next := (53361)
      square := (1631410657245666265650896323725000000000000)
      linear := (-33800829780869600804420671048443000000000000)
      constant := (165687092118934384689665155667957306927579106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223580779315343430439/100000000000000000000)
  centralHi := (5589519482883585761/2500000000000000000)
  directionLo := (229102123785920229513/100000000000000000000)
  directionHi := (114551061892960114757/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree022.table
  base := (-6566081554749375655817937020416588436499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (4667544)
      previous := (2333772)
      next := (2333772)
      square := (71350621472265007254748292108700000000000000)
      linear := (-1544698680803612266192567814059686000000000000)
      constant := (7934789429786523988358040219260695821427079327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree022.table
  base := (-6602832415074908780725114398506700828747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (518616)
      previous := (259308)
      next := (259308)
      square := (7927846830251667472749810234300000000000000)
      linear := (-172082611179440573084477478786354000000000000)
      constant := (886249809169029628782775370988744233930535359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229102123785920229513/100000000000000000000)
  centralHi := (114551061892960114757/50000000000000000000)
  directionLo := (234493499626710187481/100000000000000000000)
  directionHi := (117246749813355093741/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree023.table
  base := (-6759073434706430307477003087253287133443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-195410266242323499937679976488604906000000000000)
      constant := (1052717352578175542262295002888068707755035167319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree023.table
  base := (-6793693159270288687241703706724432671687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-21769103994273293413444195289813184000000000000)
      constant := (117582664388799580988749289248633471537366463219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234493499626710187481/100000000000000000000)
  centralHi := (117246749813355093741/50000000000000000000)
  directionLo := (119881837251462685733/50000000000000000000)
  directionHi := (239763674502925371467/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree024.table
  base := (-3440920192154161973749150126821618927021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-11328444005967217537003291526443767000000000000)
      constant := (63892336165912133472846319026466277343108796177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree024.table
  base := (-6914395640485610494217915751974946076163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-7572070678611425827888871882159178000000000000)
      constant := (42819266537560513807295458361335058691007049077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119881837251462685733/50000000000000000000)
  centralHi := (239763674502925371467/100000000000000000000)
  directionLo := (7653764765974877899/3125000000000000000)
  directionHi := (244920472511196092769/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree025.table
  base := (-3470022616613294236539696706003778836497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-106206858986248165697219259231685353000000000000)
      constant := (626049598306772449571942137021259006553335486701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree025.table
  base := (-6970608726211279504159432514369309331543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-23663320077395261553889036003141884000000000000)
      constant := (139856691805941926265459317692121622901072388291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/3125000000000000000)
  centralHi := (244920472511196092769/100000000000000000000)
  directionLo := (24997091050574339969/10000000000000000000)
  directionHi := (249970910505743399691/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree026.table
  base := (-6938768783147398612122309221690199315739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-220915443837582747122817789450753606000000000000)
      constant := (1358788935310714964620876331034763629323989129487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree026.table
  base := (-6967418049490673012547586173419794305117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-24610428118956245624111456359806234000000000000)
      constant := (151774908518988550473686520754610557816049312129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/10000000000000000000)
  centralHi := (249970910505743399691/100000000000000000000)
  directionLo := (254921310099868251457/100000000000000000000)
  directionHi := (127460655049934125729/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree027.table
  base := (-215080560357151604854164766740089992971/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-2124233052802492248622195004056819500000000000)
      constant := (13611994852121014473653813966566645021216576872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree027.table
  base := (-1727348513202386590195102910774107659877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-2129794680043102474527823059705882000000000000)
      constant := (13684038860271433471996090730645626656044874083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254921310099868251457/100000000000000000000)
  centralHi := (127460655049934125729/50000000000000000000)
  directionLo := (129888695223060122579/50000000000000000000)
  directionHi := (259777390446120245159/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree028.table
  base := (-846947786959963185895611824827277028169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400207500000000000000000000000000000000000000
      center := (2881494)
      previous := (1440747)
      next := (1440747)
      square := (44048087745632989172574200740575000000000000)
      linear := (-1213871916162018258059062915436323500000000000)
      constant := (8091767789044598015576562067234533022999243946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree028.table
  base := (-1360129733137647907736675421567273895091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1280664)
      previous := (640332)
      next := (640332)
      square := (19576927886947995187810755884700000000000000)
      linear := (-540911106164861505399108103533366000000000000)
      constant := (3615383294145292729667485044985712496140081915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129888695223060122579/50000000000000000000)
  centralHi := (259777390446120245159/100000000000000000000)
  directionLo := (264544345679432016591/100000000000000000000)
  directionHi := (16534021604964501037/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree029.table
  base := (-165537064868838167429135025768076815207/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-61605155358210498576988900603225576500000000000)
      constant := (426608258623773593964585404976224996003696731310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree029.table
  base := (-6644883803586163630676573818716989751251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-27451752243639197834778717429799284000000000000)
      constant := (190607627336031426039977128073204981511430424687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264544345679432016591/100000000000000000000)
  centralHi := (16534021604964501037/6250000000000000000)
  directionLo := (67306727503144901127/25000000000000000000)
  directionHi := (269226910012579604509/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree030.table
  base := (-6423612780173911573645715587614381503507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-28324705255325378892926097044476134000000000000)
      constant := (203489881757444801538992885533226816813658928559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree030.table
  base := (-257817345732141293186433895244310867097/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-9466286761733393968333712595487878000000000000)
      constant := (68189032715619641291979477225370029064502811575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67306727503144901127/25000000000000000000)
  centralHi := (269226910012579604509/100000000000000000000)
  directionLo := (273829412808201542803/100000000000000000000)
  directionHi := (68457353202050385701/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree031.table
  base := (-3092488595856918148119981410058179508213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-131712036581507412882357072193834053000000000000)
      constant := (980445312187998867544167553198691259039550177729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree031.table
  base := (-3102650963535405119077768433769772362279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-14672984163380582987611779071563992000000000000)
      constant := (109514787947506113420612557646471521015615027923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273829412808201542803/100000000000000000000)
  centralHi := (68457353202050385701/25000000000000000000)
  directionLo := (17397239090725635409/6250000000000000000)
  directionHi := (55671165090322033309/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree032.table
  base := (-1181656718735153335329952173912022905611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-271925799028101241493093415375051006000000000000)
      constant := (2094856860287469189478342152990906793114263200315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree032.table
  base := (-5927195140513022751347309568000842006859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-30293076368322150045445978499792334000000000000)
      constant := (233992701707760530927332101620439570137975949383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17397239090725635409/6250000000000000000)
  centralHi := (55671165090322033309/20000000000000000000)
  directionLo := (28280980146877880303/10000000000000000000)
  directionHi := (282809801468778803031/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree033.table
  base := (-349748293851010516789147473716463828737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18007500000000000000000000000000000000000000
      center := (129654)
      previous := (64827)
      next := (64827)
      square := (1981961707562916868187452558575000000000000)
      linear := (-64377301398803410748731103388988500000000000)
      constant := (512692492749096583777350827473214244166429556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree033.table
  base := (-5613552168766488324938381034584307683037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (172872)
      previous := (86436)
      next := (86436)
      square := (2642615610083889157583270078100000000000000)
      linear := (-86061114076813041640959776464068000000000000)
      constant := (687202065958836834743945456102950827253028163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28280980146877880303/10000000000000000000)
  centralHi := (282809801468778803031/100000000000000000000)
  directionLo := (14359735552123940163/5000000000000000000)
  directionHi := (287194711042478803261/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree034.table
  base := (-1312561164688621160540202351005211102441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-72232312689568518237462989337454201500000000000)
      constant := (594042070171990353097500067920385820263308932453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree034.table
  base := (-5266570887867345595135701639233332315169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-32187292451444118185890819213121034000000000000)
      constant := (265412605013472261997196973840715685187394360853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14359735552123940163/5000000000000000000)
  centralHi := (287194711042478803261/100000000000000000000)
  directionLo := (291513670853933900531/100000000000000000000)
  directionHi := (72878417713483475133/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree035.table
  base := (-4873082825713884875773495965643585740869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (11525976)
      previous := (5762988)
      next := (5762988)
      square := (176192350982531956690296802962300000000000000)
      linear := (-6070019931088989564861861802799994000000000000)
      constant := (51499605091684611629422044671990667863844467873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree035.table
  base := (-4888232054780903235570513020128688798003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1280664)
      previous := (640332)
      next := (640332)
      square := (19576927886947995187810755884700000000000000)
      linear := (-676212254959287801145168154485416000000000000)
      constant := (5752362052337164256311231746746437262349920639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291513670853933900531/100000000000000000000)
  centralHi := (72878417713483475133/25000000000000000000)
  directionLo := (295769570001206389031/100000000000000000000)
  directionHi := (36971196250150798629/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree036.table
  base := (-893255036677053803177355081329715599829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-11330840832905440903948537012021578000000000000)
      constant := (99081910362478350060545921641967556471110395455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree036.table
  base := (-448032079655047407714063618549719642621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-5680251422427681054389276654408289000000000000)
      constant := (49802033457587146639562758040592863498530522295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295769570001206389031/100000000000000000000)
  centralHi := (36971196250150798629/12500000000000000000)
  directionLo := (74991273151723019907/25000000000000000000)
  directionHi := (299965092606892079629/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree037.table
  base := (-2015716801784350408522326537924234775411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-157217214176766660067494885155982753000000000000)
      constant := (1415674213970337373537132312746921197497946163463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree037.table
  base := (-4044445954367781076317981844058268101193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-35028616576127070396558080283114084000000000000)
      constant := (316250583350022174196464023886637332928919925341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991273151723019907/25000000000000000000)
  centralHi := (299965092606892079629/100000000000000000000)
  directionLo := (76025684404443277431/25000000000000000000)
  directionHi := (12164109504710924389/4000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree038.table
  base := (-3570011208275406175092978990815052280651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-322936154218619735863369041299348406000000000000)
      constant := (2991879795567408625481104543199913523302070752383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree038.table
  base := (-179102875238591080400634938611247067341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-8993931154422013616695125159944608500000000000)
      constant := (83544906158029168366860992130449751361235380085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76025684404443277431/25000000000000000000)
  centralHi := (12164109504710924389/4000000000000000000)
  directionLo := (308184836211301887999/100000000000000000000)
  directionHi := (601923508225199/195312500000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree039.table
  base := (-3083318011981898712829663309641347686603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-36826431120411794621305368031859034000000000000)
      constant := (350755045202865816007957789190141684086221229511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree039.table
  base := (-3094462253611129516895633490114664558863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-12307610886416346179000973665480928000000000000)
      constant := (117532728542726870649017841714476358287694562377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308184836211301887999/100000000000000000000)
  centralHi := (601923508225199/195312500000000)
  directionLo := (62442713430647706433/20000000000000000000)
  directionHi := (156106783576619266083/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree040.table
  base := (-160783438706286822698260270010882898537/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-84984901487198141830031895818528551500000000000)
      constant := (831521499459129711006321913937087985258886280084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree040.table
  base := (-516567595303050585062949198905252715751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-37869940700810022607225341353107134000000000000)
      constant := (371505239832552973785134738692837566136509555935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62442713430647706433/20000000000000000000)
  centralHi := (156106783576619266083/50000000000000000000)
  directionLo := (63238194078740927157/20000000000000000000)
  directionHi := (158095485196852317893/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree041.table
  base := (-127420433253008866760364577698295536233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-87110332953469745762126713565374276500000000000)
      constant := (874935804251800797131648137574243955111949681556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree041.table
  base := (-2048246161037457407206848695724926343417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-38817048742371006677447761709771484000000000000)
      constant := (390899862091957372178270519135296521271352449229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63238194078740927157/20000000000000000000)
  centralHi := (158095485196852317893/50000000000000000000)
  directionLo := (160059479571248307053/50000000000000000000)
  directionHi := (320118959142496614107/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree042.table
  base := (-1482853603694979261835544073038497823807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1280664)
      previous := (640332)
      next := (640332)
      square := (19576927886947995187810755884700000000000000)
      linear := (-809394688614434010831941327094966000000000000)
      constant := (8339590782727694334432518356187086239207944891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree042.table
  base := (-745821744758661915185112911065086839477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (213444)
      previous := (106722)
      next := (106722)
      square := (3262821314491332531301792647450000000000000)
      linear := (-135252233958952349481871367572911000000000000)
      constant := (1397215029243074404784285681883782100128740867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160059479571248307053/50000000000000000000)
  centralHi := (320118959142496614107/100000000000000000000)
  directionLo := (161999665313264020641/50000000000000000000)
  directionHi := (323999330626528041283/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree043.table
  base := (-452890182563557031317739246971928421349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-182722391772025907252632698118131453000000000000)
      constant := (1930064082325100914886662526266059125343734213617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree043.table
  base := (-114236523442823346277497173518492678811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-10177816206373243704473150605775046000000000000)
      constant := (107787139466288139890077660473647033493254896814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161999665313264020641/50000000000000000000)
  centralHi := (323999330626528041283/100000000000000000000)
  directionLo := (65566755140208378817/20000000000000000000)
  directionHi := (163916887850520947043/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree044.table
  base := (-308287333189147225304793830378423651243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (4667544)
      previous := (2333772)
      next := (2333772)
      square := (71350621472265007254748292108700000000000000)
      linear := (-3090467019910233307716071629947486000000000000)
      constant := (33444983356365885908389322356041141929960870039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree044.table
  base := (-315769350315339156054032901204321878657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (518616)
      previous := (259308)
      next := (259308)
      square := (7927846830251667472749810234300000000000000)
      linear := (-344284073281437676761281179998054000000000000)
      constant := (3735547128988411604295246132746151269508033629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65566755140208378817/20000000000000000000)
  centralHi := (163916887850520947043/50000000000000000000)
  directionLo := (331623887460423848267/100000000000000000000)
  directionHi := (82905971865105962067/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree045.table
  base := (61784439528630256665458418147621539981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-14164749454600912813408294007815878000000000000)
      constant := (156959203070523541756062714464190085787084100505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree045.table
  base := (37753081499510873551920346218499862599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-3550456742384578579861453594702407000000000000)
      constant := (39444878534006215560103307975183453034664248158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331623887460423848267/100000000000000000000)
  centralHi := (82905971865105962067/25000000000000000000)
  directionLo := (335371168973015145659/100000000000000000000)
  directionHi := (16768558448650757283/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree046.table
  base := (945214190073786207989748726388741879311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-390949961139311061690403209198411606000000000000)
      constant := (4433289681570761841655052842150108985347021397837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree046.table
  base := (187771719778688148024531187047127503451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-43552588950175927028559863493093234000000000000)
      constant := (495160027118151790295595599644081041941451319565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335371168973015145659/100000000000000000000)
  centralHi := (16768558448650757283/5000000000000000000)
  directionLo := (8476926006161132721/2500000000000000000)
  directionHi := (339077040246445308841/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree047.table
  base := (800008521919591415801684825512151481047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-199725843502198738709391240092897253000000000000)
      constant := (2316506049224693069949455660211534966531481898149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree047.table
  base := (1594163592175799915506211056636861550703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-44499696991736911098782283849757584000000000000)
      constant := (517465160907206724501720964132975347213715358789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8476926006161132721/2500000000000000000)
  centralHi := (339077040246445308841/100000000000000000000)
  directionLo := (171371422257513742957/50000000000000000000)
  directionHi := (68548568903005497183/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree048.table
  base := (1136407723602592616643727679747920751053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-22664078492749105174842319509620967000000000000)
      constant := (268725649522235550939635212190375553053550005839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree048.table
  base := (35428545354363473278155546528759593207/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-3787233752774824597417058683868494500000000000)
      constant := (45021124741622592602074478273060394252449453552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171371422257513742957/50000000000000000000)
  centralHi := (68548568903005497183/20000000000000000000)
  directionLo := (173184926964080163439/50000000000000000000)
  directionHi := (346369853928160326879/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree049.table
  base := (1481572416976194324442426354446187793147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (117612)
      previous := (58806)
      next := (58806)
      square := (1797881132474815884594865336350000000000000)
      linear := (-86725351673171659490949817192953000000000000)
      constant := (1050694464043059605378686470507897695520211249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree049.table
  base := (739546606139369157309593707005892959923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (6534)
      previous := (3267)
      next := (3267)
      square := (99882285137489771366381407575000000000000)
      linear := (-4830686492592553023659633961171000000000000)
      constant := (58676034187899540508616651812067451644452049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173184926964080163439/50000000000000000000)
  centralHi := (346369853928160326879/100000000000000000000)
  directionLo := (174979637354020379783/50000000000000000000)
  directionHi := (349959274708040759567/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree050.table
  base := (367058638621594511334469769113180001461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-212478432299828362301960146573971603000000000000)
      constant := (2629064094008795199930647260296139847572600909435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree050.table
  base := (3666025677111147962936772931818054522467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-47341021116419863309449544919750634000000000000)
      constant := (587278204241387232338598767930052089053764905921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174979637354020379783/50000000000000000000)
  centralHi := (349959274708040759567/100000000000000000000)
  directionLo := (88378062958993375947/25000000000000000000)
  directionHi := (353512251835973503789/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree051.table
  base := (549345316177812274465985731782908549053/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-12040516401798420564786099003759058500000000000)
      constant := (152087190131345653809799802189603447747476559678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree051.table
  base := (2195284650050797827249034397234417292883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-8048021526330141229945327546069164000000000000)
      constant := (101918980908629256982487529877390538521345662043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88378062958993375947/25000000000000000000)
  centralHi := (353512251835973503789/100000000000000000000)
  directionLo := (178514936659445648009/50000000000000000000)
  directionHi := (357029873318891296019/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree052.table
  base := (10270665741725730023057066337894037373/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-110490079082457389015169708780677251500000000000)
      constant := (1424116029101028623710407522464721736506789498875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree052.table
  base := (5131478993823461664455660717784432351149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-49235237199541831449894385633079334000000000000)
      constant := (636231381122246014744781928230088371213264475887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178514936659445648009/50000000000000000000)
  centralHi := (357029873318891296019/100000000000000000000)
  directionLo := (22532073380071945891/6250000000000000000)
  directionHi := (360513174081151134257/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree053.table
  base := (1178398107642499721765286316705075678137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-450462042194915971789058106110091906000000000000)
      constant := (5922101595917529080892298263080625932296885315895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree053.table
  base := (5888449860023493309342649313806630329859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-50182345241102815520116805989743684000000000000)
      constant := (661430425514762351219608553596020481400182899617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22532073380071945891/6250000000000000000)
  centralHi := (360513174081151134257/100000000000000000000)
  directionLo := (90990784880265896151/25000000000000000000)
  directionHi := (72792627904212716921/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree054.table
  base := (6664458878614553057156253678496333038483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-16998658076296384722868051003610178000000000000)
      constant := (227853670858708979793242593667978895170673119643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree054.table
  base := (6661207104088543651603455183232327500999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-17043151094221266530113075448802678000000000000)
      constant := (229036926376169044378356100638048251017917730479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90990784880265896151/25000000000000000000)
  centralHi := (72792627904212716921/20000000000000000000)
  directionLo := (22961294297924633697/6250000000000000000)
  directionHi := (367380708766794139153/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree055.table
  base := (7452488482819138726541607162242704662321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (4667544)
      previous := (2333772)
      next := (2333772)
      square := (71350621472265007254748292108700000000000000)
      linear := (-3863351189463543828477823537891386000000000000)
      constant := (52779377783670149267911118662558437815144283467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree055.table
  base := (3724751531416870522267233777800684626443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (259308)
      previous := (129654)
      next := (129654)
      square := (3963923415125833736374905117150000000000000)
      linear := (-215192402166218114299841515301952000000000000)
      constant := (2947405893014099025636963777150936456364268929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22961294297924633697/6250000000000000000)
  centralHi := (367380708766794139153/100000000000000000000)
  directionLo := (92691694415530977999/25000000000000000000)
  directionHi := (370766777662123911997/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree056.table
  base := (8255854502368993793736139394967827678463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (11525976)
      previous := (5762988)
      next := (5762988)
      square := (176192350982531956690296802962300000000000000)
      linear := (-9713616730411739162738692225964094000000000000)
      constant := (135201359757306169255373422507568498758251392429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree056.table
  base := (4126557262871803639011059894007712773497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (640332)
      previous := (320166)
      next := (320166)
      square := (9788463943473997593905377942350000000000000)
      linear := (-541057850671283344191674153670783000000000000)
      constant := (7550148693014799415220389179399813187102191139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92691694415530977999/25000000000000000000)
  centralHi := (370766777662123911997/100000000000000000000)
  directionLo := (374122201508969047881/100000000000000000000)
  directionHi := (187061100754484523941/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree057.table
  base := (9074354230974017751977868385401143829803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-53829882850584626078063910006624834000000000000)
      constant := (763081474666129364543770235927440765119734592089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree057.table
  base := (9071840320692932358502060116612665884553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-17990259135782250600335495805467028000000000000)
      constant := (255679213737480434733268697109914418055446222113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374122201508969047881/100000000000000000000)
  centralHi := (187061100754484523941/50000000000000000000)
  directionLo := (188723898795224433259/50000000000000000000)
  directionHi := (377447797590448866519/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree058.table
  base := (9907804924058872815864031428159683378797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-492970671520348050430954461047006406000000000000)
      constant := (7114903210024881187422817726951777041122070047399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree058.table
  base := (2476374784508705423018648584027372430367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-13729471362226933967807226943266358500000000000)
      constant := (198660318994401268083956522533892929297527953621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188723898795224433259/50000000000000000000)
  centralHi := (377447797590448866519/100000000000000000000)
  directionLo := (38074434749559089443/10000000000000000000)
  directionHi := (380744347495590894431/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree059.table
  base := (2689010458257438784735620854515183886243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-125368099346358616539833433008597326500000000000)
      constant := (1841593787474536264985881543796627918421010470281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree059.table
  base := (10753927569521484385014385854933735539999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-55864993490468719941451328129729784000000000000)
      constant := (822725333790358977724950200462906673598448148437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38074434749559089443/10000000000000000000)
  centralHi := (380744347495590894431/100000000000000000000)
  directionLo := (192006299632203531017/50000000000000000000)
  directionHi := (76802519852881412407/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree060.table
  base := (1161891643311604159192209555486498687183/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-28331895736140048993761833501209567000000000000)
      constant := (423452662587594665055452677290914666276486385145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree060.table
  base := (5808489170423464137567206478352541604003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-9468683588671617335278958081065689000000000000)
      constant := (141881614381977844486721035850592423739336555563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192006299632203531017/50000000000000000000)
  centralHi := (76802519852881412407/20000000000000000000)
  directionLo := (387253269370019524797/100000000000000000000)
  directionHi := (193626634685009762399/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree061.table
  base := (6248147412862340175546320139785557574207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-259237924557803648808046137004577553000000000000)
      constant := (3941110244875511408173514280771790587244437179869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree061.table
  base := (12494518718694906954486401952800453224687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-57759209573590688081896168843058484000000000000)
      constant := (880334217796682032253903512796637926663867875781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387253269370019524797/100000000000000000000)
  centralHi := (193626634685009762399/50000000000000000000)
  directionLo := (78093408910542947899/20000000000000000000)
  directionHi := (48808380569089342437/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree062.table
  base := (2677611259624463040131236068109039203741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-526977574980693713344471544996538006000000000000)
      constant := (8146591892542333396698581807844250856098855273235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree062.table
  base := (6693214537531440136675218510092636135553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-29353158807575836076059294599861417000000000000)
      constant := (454929412020731547912585877273842672228210979339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78093408910542947899/20000000000000000000)
  centralHi := (48808380569089342437/12500000000000000000)
  directionLo := (196827291759612526273/50000000000000000000)
  directionHi := (393654583519225052547/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree063.table
  base := (3573523006238101784257889245011451859267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14822500000000000000000000000000000000000000
      center := (106722)
      previous := (53361)
      next := (53361)
      square := (1631410657245666265650896323725000000000000)
      linear := (-101186564785672737920039836731655500000000000)
      constant := (1590185427308625797660733953307844398073594043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree063.table
  base := (7146300796666909109855015837779796944071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (213444)
      previous := (106722)
      next := (106722)
      square := (3262821314491332531301792647450000000000000)
      linear := (-202902808356165497354901393048936000000000000)
      constant := (3196814323323932207842747671251198791081396959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196827291759612526273/50000000000000000000)
  centralHi := (393654583519225052547/100000000000000000000)
  directionLo := (198408259259574012443/50000000000000000000)
  directionHi := (396816518519148024887/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree064.table
  base := (7607151948810123029302838605480246908781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-271990513355433272400615043485651903000000000000)
      constant := (4344113943252687804015232735629013015929021052327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree064.table
  base := (7606469551050398867113414442683490620643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-30300266849136820146281714956525767000000000000)
      constant := (485173947076499010006662789362950839135799475009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198408259259574012443/50000000000000000000)
  centralHi := (396816518519148024887/100000000000000000000)
  directionLo := (24997091050574339969/6250000000000000000)
  directionHi := (79990691361837887901/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree065.table
  base := (4037150867238535115801654319027727023561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-138120688143988240132402339489671676500000000000)
      constant := (2241372753580294087120449690858198150630523062587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree065.table
  base := (1614735402413109503091001043662883664513/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-30773820869917312181392925134857942000000000000)
      constant := (500656098499836632053377764593837390001469719095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/6250000000000000000)
  centralHi := (79990691361837887901/20000000000000000000)
  directionLo := (403065982014834610217/100000000000000000000)
  directionHi := (201532991007417305109/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree066.table
  base := (8548455500895514175402293404488130739291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (259308)
      previous := (129654)
      next := (129654)
      square := (3963923415125833736374905117150000000000000)
      linear := (-257568631056491908291087524768627000000000000)
      constant := (4245661175069329887199823819925835005715113073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree066.table
  base := (17095767429101807042764471829132798407743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (172872)
      previous := (86436)
      next := (86436)
      square := (2642615610083889157583270078100000000000000)
      linear := (-172161845127811593479361627069918000000000000)
      constant := (2845058542161192234215642458594085848976990943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403065982014834610217/100000000000000000000)
  centralHi := (201532991007417305109/50000000000000000000)
  directionLo := (126923329811904877/31250000000000000)
  directionHi := (406154655398095606401/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree067.table
  base := (3611830922250521036040590329873040711453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-569486204306125791986367899933452506000000000000)
      constant := (9532904397575046337881167361828024466171824996755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree067.table
  base := (4514527044965353446164632988362335130133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-15860464455739148125807672745761146000000000000)
      constant := (266169998391751845135273076297264775455524107879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126923329811904877/31250000000000000)
  centralHi := (406154655398095606401/100000000000000000000)
  directionLo := (204610008519566686143/50000000000000000000)
  directionHi := (409220017039133372287/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree068.table
  base := (19035269491485838580918752445073108835391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-577987930171212207714747170920835406000000000000)
      constant := (9823053580801860701094414854004490393603098975197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree068.table
  base := (4758578040745814486890382566641030422103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-16097241466129394143363277834927233500000000000)
      constant := (274270842352066646236241779437760346897779356989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204610008519566686143/50000000000000000000)
  centralHi := (409220017039133372287/100000000000000000000)
  directionLo := (103065646734699937609/25000000000000000000)
  directionHi := (412262586938799750437/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree069.table
  base := (1001259860927513717834154848486479420193/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-16291379334341628428975734497450508500000000000)
      constant := (281041586963892784923194289324678831314508358295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree069.table
  base := (1251520099705538100225490675192109834029/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-5444672825506546720306294308031107000000000000)
      constant := (94163860663884149236648525858995429201867756436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103065646734699937609/25000000000000000000)
  centralHi := (412262586938799750437/100000000000000000000)
  directionLo := (83056573209694664749/20000000000000000000)
  directionHi := (207641433024236661873/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree070.table
  base := (2628610640244200810814569304951331607373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 400207500000000000000000000000000000000000000
      center := (2881494)
      previous := (1440747)
      next := (1440747)
      square := (44048087745632989172574200740575000000000000)
      linear := (-3035670315823393056997478127018373500000000000)
      constant := (53144054255709257320866530541788130535406183918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree070.table
  base := (21028084398838663020673933404037674986059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1280664)
      previous := (640332)
      next := (640332)
      square := (19576927886947995187810755884700000000000000)
      linear := (-1352717998931419279875468409245666000000000000)
      constant := (23741404568425151405821042375448238124977031433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83056573209694664749/20000000000000000000)
  centralHi := (207641433024236661873/50000000000000000000)
  directionLo := (209140668616482296941/50000000000000000000)
  directionHi := (418281337232964593883/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree071.table
  base := (22046285718075395375233908119620239340939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-603493107766471454899884983882984106000000000000)
      constant := (10719265718593783103304865848030982597946361358913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree071.table
  base := (22045553637635366238661120983326700935211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-67230289989200528784120372409701984000000000000)
      constant := (1197170816159255198920813950152138939697195304793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209140668616482296941/50000000000000000000)
  centralHi := (418281337232964593883/100000000000000000000)
  directionLo := (210629233085865758997/50000000000000000000)
  directionHi := (84251693234346303599/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree072.table
  base := (2307735619938451602445250473892313321661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-11333237659843664270893782497599389000000000000)
      constant := (204196112006283407655692288468810451792611376905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree072.table
  base := (2307668700993842181705367681774907642707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-11362899671793585475723798794394389000000000000)
      constant := (205248711336207742014730452421299297716334401735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210629233085865758997/50000000000000000000)
  centralHi := (84251693234346303599/20000000000000000000)
  directionLo := (84842940440633640909/20000000000000000000)
  directionHi := (212107351101584102273/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree073.table
  base := (753814311686126920928383470578473069163/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-155124139874161071589160881464437476500000000000)
      constant := (2834551830159483133999842591116282919097681647368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree073.table
  base := (12060723195353668905399925078693398790579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-34562253036161248462282606561515342000000000000)
      constant := (633146573099215756053416115242541711355113404977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84842940440633640909/20000000000000000000)
  centralHi := (212107351101584102273/50000000000000000000)
  directionLo := (213575239558150500611/50000000000000000000)
  directionHi := (427150479116301001223/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree074.table
  base := (12590178125167236021346209480207739624393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-314499142680865351042511398422566403000000000000)
      constant := (5827058631291580116760057149396466730532293526331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree074.table
  base := (3147474677402444705715342761814669822001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-17517903528470870248696908369923758500000000000)
      constant := (325393355188818986350175789370322624648145315126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213575239558150500611/50000000000000000000)
  centralHi := (427150479116301001223/100000000000000000000)
  directionLo := (430066215893841529743/100000000000000000000)
  directionHi := (26879138493365095609/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree075.table
  base := (1050088786531097095485960992749652848909/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-70833334580757457534822451981390634000000000000)
      constant := (1330479958682658319317742227358974192148841869175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree075.table
  base := (26251709127404319877567113101659926557457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-23672907385148155021670017945453128000000000000)
      constant := (445777688232385031637785355396042412273398965097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430066215893841529743/100000000000000000000)
  centralHi := (26879138493365095609/6250000000000000000)
  directionLo := (432962317410200408597/100000000000000000000)
  directionHi := (216481158705100204299/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree076.table
  base := (27337619936354772228366397852262705377613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-646001737091903533541781338819898606000000000000)
      constant := (12298814195518013798222825698607415718583256672071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree076.table
  base := (5467430720974455727179052063480158857057/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-71965830197005449135232474193023734000000000000)
      constant := (1373572053698406291189914660986591322469665850455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432962317410200408597/100000000000000000000)
  centralHi := (216481158705100204299/50000000000000000000)
  directionLo := (435839175087754064191/100000000000000000000)
  directionHi := (6809987110746157253/1562500000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree077.table
  base := (28436531577773178574734716508323328893939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13230000000000000000000000000000000000000000
      center := (95256)
      previous := (47628)
      next := (47628)
      square := (1456135132087040964382618206300000000000000)
      linear := (-110390194460615609591863823546514000000000000)
      constant := (2129802793851592543715700519110439764126681297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree077.table
  base := (28436105697017815910981571738356389935537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1470000000000000000000000000000000000000000
      center := (10584)
      previous := (5292)
      next := (5292)
      square := (161792792454115662709179800700000000000000)
      linear := (-12297678906825170046458912894196000000000000)
      constant := (237863107747546972167476548878761639320523939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435839175087754064191/100000000000000000000)
  centralHi := (6809987110746157253/1562500000000000000)
  directionLo := (219348583757188159971/50000000000000000000)
  directionHi := (438697167514376319943/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree078.table
  base := (5909786321230928090916788214760129738787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-73667243202452929444282208977184934000000000000)
      constant := (1440075461728965691454909798935946516777632070405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree078.table
  base := (14774271366464345259091829692542406465743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-12310007713354569545946219151058739000000000000)
      constant := (241247996891404321603817830756726704468834122103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219348583757188159971/50000000000000000000)
  centralHi := (438697167514376319943/100000000000000000000)
  directionLo := (220768330512496500241/50000000000000000000)
  directionHi := (441536661024993000483/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree079.table
  base := (958587478228721771873399337402114280473/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19610167500000000000000000000000000000000000000
      center := (141193206)
      previous := (70596603)
      next := (70596603)
      square := (2158356299536016469456135836288175000000000000)
      linear := (-167876728671790695181729787945511826500000000000)
      constant := (3324512301361754593642151781610158541361496029528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree079.table
  base := (30674444280160064521452905709830706228233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-74807154321688401345899735263016784000000000000)
      constant := (1485164882429903165829673898445364422062397438179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220768330512496500241/50000000000000000000)
  centralHi := (441536661024993000483/100000000000000000000)
  directionLo := (444358010249688632753/100000000000000000000)
  directionHi := (222179005124844316377/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree080.table
  base := (31814115991411948365333131483799015370039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-680008640552249196455298422769430206000000000000)
      constant := (13639710767894730755727044443386983371096615708613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree080.table
  base := (7953447980930128270826653497779282927737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-18938565590812346354030538904920283500000000000)
      constant := (380830263257453133848909567103632435166347242931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444358010249688632753/100000000000000000000)
  centralHi := (222179005124844316377/50000000000000000000)
  directionLo := (447161558630686860879/100000000000000000000)
  directionHi := (5589519482883585761/1250000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree081.table
  base := (16483432415989552260944886787268181975913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-12750191970691400225623660995496539000000000000)
      constant := (258993772422627153720361671688988073495824220673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree081.table
  base := (32966569066879500829560804025769762768917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-25567123468270123162114858658781828000000000000)
      constant := (520652159561019260906156727370012318999388535757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447161558630686860879/100000000000000000000)
  centralHi := (5589519482883585761/1250000000000000000)
  directionLo := (224973819455169059721/50000000000000000000)
  directionHi := (449947638910338119443/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree082.table
  base := (6826606128965654026680218548002855984743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-697012092282422027912056964744196006000000000000)
      constant := (14335907915153979574938206232206536734678375348905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree082.table
  base := (34132760751641829289230815829643857477979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-77648478446371353556566996333009834000000000000)
      constant := (1601071146352803738633202836322124927355079811177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224973819455169059721/50000000000000000000)
  centralHi := (449947638910338119443/100000000000000000000)
  directionLo := (113179143398019350223/25000000000000000000)
  directionHi := (452716573592077400893/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree083.table
  base := (7062519948945604372897848710023410343981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-705513818147508443640436235731578906000000000000)
      constant := (14690443273543198382695005036521054209533400053635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree083.table
  base := (17656176748473639281018006283348475185479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-39297793243966168813394708344837092000000000000)
      constant := (820332522144728557351443969184030986203081633677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113179143398019350223/25000000000000000000)
  centralHi := (452716573592077400893/100000000000000000000)
  directionLo := (11386716884403995319/2500000000000000000)
  directionHi := (455468675376159812761/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree084.table
  base := (9126389948547022824593677706438111804867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44467500000000000000000000000000000000000000
      center := (320166)
      previous := (160083)
      next := (160083)
      square := (4894231971736998796952688971175000000000000)
      linear := (-404770716560427924812253688616191500000000000)
      constant := (8531332023363618167154605579850675694673169329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree084.table
  base := (18252667576422691404611212677169150045633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (213444)
      previous := (106722)
      next := (106722)
      square := (3262821314491332531301792647450000000000000)
      linear := (-270553382753378645227931418524961000000000000)
      constant := (5716796469059764058060216200226634890620558057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11386716884403995319/2500000000000000000)
  centralHi := (455468675376159812761/100000000000000000000)
  directionLo := (229102123785920229513/50000000000000000000)
  directionHi := (458204247571840459027/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree085.table
  base := (37711899670737254020347312405993749592441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-722517269877681275097194777706344706000000000000)
      constant := (15412387074919242277554341396760635933384329897547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree085.table
  base := (1508467790762722681420690559261901138897/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-80489802571054305767234257403002884000000000000)
      constant := (1721290489651295799486544770963143429808012150275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229102123785920229513/50000000000000000000)
  centralHi := (458204247571840459027/100000000000000000000)
  directionLo := (460923584487536586967/100000000000000000000)
  directionHi := (57615448060942073371/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree086.table
  base := (38931609347271167986596180381578784439631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-731018995742767690825574048693727606000000000000)
      constant := (15779795352007379599793287115024783816923023019277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree086.table
  base := (19465711238289300390870273249921718275911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-40718455306307644918728338879833617000000000000)
      constant := (881161009465572677022108640025318084545707818893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460923584487536586967/100000000000000000000)
  centralHi := (57615448060942073371/12500000000000000000)
  directionLo := (46362697180039266269/10000000000000000000)
  directionHi := (463626971800392662691/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree087.table
  base := (8032935956836618591136351381341047509179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-82168969067539345172661479964567834000000000000)
      constant := (1794610494396728165496901481050687394951212883885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree087.table
  base := (10041127345203919278924836864995326736077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (5229378)
      previous := (2614689)
      next := (2614689)
      square := (79939122205037647016893919862525000000000000)
      linear := (-6865334887848022825639924843027632000000000000)
      constant := (150319395165912396699081518953815733506191826117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46362697180039266269/10000000000000000000)
  centralHi := (463626971800392662691/100000000000000000000)
  directionLo := (466314686906561960053/100000000000000000000)
  directionHi := (233157343453280980027/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree088.table
  base := (4141110283211716674059099516398686821989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2333772)
      previous := (1166886)
      next := (1166886)
      square := (35675310736132503627374146054350000000000000)
      linear := (-3091001849061737695381539630861543000000000000)
      constant := (68295389684647398994847616408864172353045404515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree088.table
  base := (10352736866369480183356361699756267421913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18007500000000000000000000000000000000000000
      center := (129654)
      previous := (64827)
      next := (64827)
      square := (1981961707562916868187452558575000000000000)
      linear := (-172171749371357971028722145605363500000000000)
      constant := (3813683164966930460654494130921257394240039339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466314686906561960053/100000000000000000000)
  centralHi := (233157343453280980027/50000000000000000000)
  directionLo := (468986999253420374963/100000000000000000000)
  directionHi := (117246749813355093741/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree089.table
  base := (42670871144298176957053774097970691186709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-756524173338026938010711861655876306000000000000)
      constant := (16907764856721133801754872063834529349704854905503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree089.table
  base := (21335364752904067612653952714800701232681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (31376268)
      previous := (15688134)
      next := (15688134)
      square := (479634733230225882101363519175150000000000000)
      linear := (-42139117368649121024061969414830142000000000000)
      constant := (944145871096725522686629168453563572193459150403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468986999253420374963/100000000000000000000)
  centralHi := (117246749813355093741/25000000000000000000)
  directionLo := (471644170654838623313/100000000000000000000)
  directionHi := (235822085327419311657/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree090.table
  base := (43943978097494777861968086108111340185809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-28334292563078272360707078986787378000000000000)
      constant := (640456890989884177480307521210044384662121416489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree090.table
  base := (21971924495219674851656924368323046577411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-14204223796476537686391059864387439000000000000)
      constant := (321873334560708722731723527295229214814716021131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471644170654838623313/100000000000000000000)
  centralHi := (235822085327419311657/50000000000000000000)
  directionLo := (237143227795278476839/50000000000000000000)
  directionHi := (474286455590556953679/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree091.table
  base := (22615208860382984413567709424048487121317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (5762988)
      previous := (2881494)
      next := (2881494)
      square := (88096175491265978345148401481150000000000000)
      linear := (-7893139031308160912933371465618797000000000000)
      constant := (180420386294545165973661071197044280963841789311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree091.table
  base := (11307575012739332590847222569142338506819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44467500000000000000000000000000000000000000
      center := (320166)
      previous := (160083)
      next := (160083)
      square := (4894231971736998796952688971175000000000000)
      linear := (-439655361328674541778412140525454000000000000)
      constant := (10074833888988293373219696871156625337520789553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237143227795278476839/50000000000000000000)
  centralHi := (474286455590556953679/100000000000000000000)
  directionLo := (476914101490631296323/100000000000000000000)
  directionHi := (119228525372657824081/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree092.table
  base := (46530184631224372898480535351166070434253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-782029350933286185195849674618025006000000000000)
      constant := (18074350214913064983824295695943798636612999626951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree092.table
  base := (46530077398417684784305849106046668089099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-87119558861981194258791199899653334000000000000)
      constant := (2018574042216162298163594580328590230179739391737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476914101490631296323/100000000000000000000)
  centralHi := (119228525372657824081/25000000000000000000)
  directionLo := (119881837251462685733/25000000000000000000)
  directionHi := (479527349005850742933/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree093.table
  base := (47843273976125331302300874920405622998159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-87836786310930288991580993956156434000000000000)
      constant := (2052421454756059412207974944932602597997144452517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree093.table
  base := (23921588133065454281402867786779971376887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (10458756)
      previous := (5229378)
      next := (5229378)
      square := (159878244410075294033787839725050000000000000)
      linear := (-14677777817257029721502270042719614000000000000)
      constant := (343826633855525420483620921619900702939384588127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119881837251462685733/25000000000000000000)
  centralHi := (479527349005850742933/100000000000000000000)
  directionLo := (241063216132481418517/50000000000000000000)
  directionHi := (96425286452992567407/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree094.table
  base := (24584840690329437274795085738737456213607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (282386412)
      previous := (141193206)
      next := (141193206)
      square := (4316712599072032938912271672576350000000000000)
      linear := (-399516401331729508326304108296395403000000000000)
      constant := (9436763228111766465310750244060440958949099619669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree094.table
  base := (49169592358096518849679017287430469356991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-89013774945103162399236040612982034000000000000)
      constant := (2107824721248441106531947827239251858164187146933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241063216132481418517/50000000000000000000)
  centralHi := (96425286452992567407/20000000000000000000)
  directionLo := (484711579119484841683/100000000000000000000)
  directionHi := (121177894779871210421/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree095.table
  base := (50509402900882974880528298930262163233191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-807534528528545432380987487580173706000000000000)
      constant := (19279550274233514136209584670111201305966086827797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree095.table
  base := (50509321802528520749658630764580040343039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-89960882986664146469458460969646384000000000000)
      constant := (2153168793187522631985357825237631059951500099957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484711579119484841683/100000000000000000000)
  centralHi := (121177894779871210421/25000000000000000000)
  directionLo := (97456602275365095679/20000000000000000000)
  directionHi := (121820752844206369599/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree096.table
  base := (12965608745322947007933613827980984662901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2178907500000000000000000000000000000000000000
      center := (15688134)
      previous := (7844067)
      next := (7844067)
      square := (239817366615112941050681759587575000000000000)
      linear := (-22667673733156440225260187737987683500000000000)
      constant := (546940681081801451815069510922853606935751984263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree096.table
  base := (51862361109969521250043571567518848684903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (20917512)
      previous := (10458756)
      next := (10458756)
      square := (319756488820150588067575679450100000000000000)
      linear := (-30302663676075043513226960442103578000000000000)
      constant := (732997338636371715145208932727996631438786704463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97456602275365095679/20000000000000000000)
  centralHi := (121820752844206369599/25000000000000000000)
  directionLo := (7653764765974877899/1562500000000000000)
  directionHi := (489840945022392185537/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree097.table
  base := (10645754883312489913757024887225665552999/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (564772824)
      previous := (282386412)
      next := (282386412)
      square := (8633425198144065877824543345152700000000000000)
      linear := (-824537980258718263837746029554939506000000000000)
      constant := (20104469165214780012764718490114295555586581034665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree097.table
  base := (10645741427108087394059251306120174429769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (62752536)
      previous := (31376268)
      next := (31376268)
      square := (959269466460451764202727038350300000000000000)
      linear := (-91855099069786114609903301682975084000000000000)
      constant := (2245294386672258398334363268481728417182663794735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell071.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/1562500000000000000)
  centralHi := (489840945022392185537/100000000000000000000)
  directionLo := (492385590431313351899/100000000000000000000)
  directionHi := (4923855904313133519/1000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree098.table
  base := (546084183170689385964000622552723280937/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8167500000000000000000000000000000000000000
      center := (58806)
      previous := (29403)
      next := (29403)
      square := (898940566237407942297432668175000000000000)
      linear := (-86738828209475705910675270777001500000000000)
      constant := (2136960036482390385842383875749703173970529475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree098.table
  base := (1365208926122936834802078152305191109967/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 907500000000000000000000000000000000000000
      center := (6534)
      previous := (3267)
      next := (3267)
      square := (99882285137489771366381407575000000000000)
      linear := (-9662870378107777871733207209458500000000000)
      constant := (238658465535887197142834744268913343729180210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell071.Kernel098
