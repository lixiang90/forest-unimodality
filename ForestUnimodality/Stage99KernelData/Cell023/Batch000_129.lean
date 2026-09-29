import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell023.Parameters
import ForestUnimodality.BinomialMassData.Q65_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q65_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q65_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q22_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_51.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree000.table
  base := (2130251730645677037511376257/100000000000000000000000000)
  polynomial :=
    { denominator := 30600000000000000000000000000000000000000
      center := (88)
      previous := (65)
      next := (0)
      square := (1752326260101003338465197591800000000000)
      linear := (6390950162361792818987993256000000000000)
      constant := (651857029577577173478481134642000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree000.table
  base := (2130251730645677037511376257/100000000000000000000000000)
  polynomial :=
    { denominator := 10200000000000000000000000000000000000000
      center := (29)
      previous := (22)
      next := (0)
      square := (584108753367001112821732530600000000000)
      linear := (2130316720787264272995997752000000000000)
      constant := (217285676525859057826160378214000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree001.table
  base := (135866844130022238498473087167438275876799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (12500216017137064455078121353900000000000000)
      constant := (1054051945431121120633234722140770866666662597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree001.table
  base := (67345215497979700112162105517052471271733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (691211396766686907988663783380000000000000)
      constant := (58043937992942242811673337814504492592592511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49431818042324279781/100000000000000000000)
  directionHi := (24715909021162139891/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree002.table
  base := (44460721651311671042222737371024529027297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (4351754560125778610868429952500000000000000)
      constant := (341616461756858765288999458346604399999998491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree002.table
  base := (87505225532951285740613486030429424580289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (954076374397572999908057044320000000000000)
      constant := (74674352048530167719405962722942311111110563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/100000000000000000000)
  centralHi := (24715909021162139891/50000000000000000000)
  directionLo := (69907147488214053033/100000000000000000000)
  directionHi := (34953573744107026517/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree003.table
  base := (59844843078837190794270656698129564401541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (1635600741122016662798532818700000000000000)
      constant := (151152377586845531919319632379584997008408141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree003.table
  base := (1170910843925142144756574818431663584173/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173400000000000000000000000000000000000000
      center := (493)
      previous := (374)
      next := (0)
      square := (9929848807239018917969453020200000000000)
      linear := (10514599105235443676775730437600000000000)
      constant := (984942653627521280710139507907452327477991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69907147488214053033/100000000000000000000)
  centralHi := (34953573744107026517/50000000000000000000)
  directionLo := (85618420359805567813/100000000000000000000)
  directionHi := (42809210179902783907/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree004.table
  base := (10351266348632482476351556912004070148411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (555047663240271377527168503600000000000000)
      constant := (154146724168570923886558137118735518736102066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree004.table
  base := (10080917227303889739506786255739536862637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (48691768062985683884757999720000000000000)
      constant := (16657185756978411239756639721372356919812558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/100000000000000000000)
  centralHi := (42809210179902783907/50000000000000000000)
  directionLo := (49431818042324279781/50000000000000000000)
  directionHi := (98863636084648559563/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree005.table
  base := (2935704797886211745181310828277047720471/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-268661157040496447828692444170000000000000)
      constant := (21461764934417312096246811214170803362835213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree005.table
  base := (3561497912455524086990530370803433517319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-165481441504914724149877261500000000000000)
      constant := (11553339974795130228721626030446307438062292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49431818042324279781/50000000000000000000)
  centralHi := (98863636084648559563/100000000000000000000)
  directionLo := (110532905394037666001/100000000000000000000)
  directionHi := (55266452697018833001/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree006.table
  base := (21210491814447696717804520130370430495737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-2161106155763490570542728630200000000000000)
      constant := (50999310849655671591170159478093489719411937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree006.table
  base := (10263314753162139263838801745181700100277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-379654651072815132184512522720000000000000)
      constant := (8217937478299869562662752672992533986940159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/100000000000000000000)
  centralHi := (55266452697018833001/50000000000000000000)
  directionLo := (60541365630898881203/50000000000000000000)
  directionHi := (121082731261797762407/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree007.table
  base := (7744860856787295911672518019961380554079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-5140012682087989472484723669750000000000000)
      constant := (55959802230903100557163467528383652463478437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree007.table
  base := (3736780052579006287081135328535586553977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-593827860640715540219147783940000000000000)
      constant := (6009187014732229710878695579860707084596118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60541365630898881203/50000000000000000000)
  centralHi := (121082731261797762407/100000000000000000000)
  directionLo := (26156859478757149407/20000000000000000000)
  directionHi := (32696074348446436759/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree008.table
  base := (5656417652346090807502708490431923523513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-7038366130530743089155354394200000000000000)
      constant := (42250590438740591562354564926840299253971939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree008.table
  base := (10877016869712349436971920883671795671491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-1616002140417231896507566090320000000000000)
      constant := (9094304952350980280924560976703446847182697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26156859478757149407/20000000000000000000)
  centralHi := (32696074348446436759/25000000000000000000)
  directionLo := (139814294976428106067/100000000000000000000)
  directionHi := (34953573744107026517/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree009.table
  base := (814660477029446401923237325276360464973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-595781305264899780388399007910000000000000)
      constant := (2219396171199754220824024776418813569394773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree009.table
  base := (7790898927189344250683035678804313556771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-2044348559553032712576836612760000000000000)
      constant := (7208128102059474209900890243963339853720457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/100000000000000000000)
  centralHi := (34953573744107026517/25000000000000000000)
  directionLo := (9268465882935802459/6250000000000000000)
  directionHi := (29659090825394567869/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree010.table
  base := (2831813164617205504046910875284129790601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-10835073027416250322496615843100000000000000)
      constant := (27803492766525135956203865452342064756059603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree010.table
  base := (5368491947569357374475666919606207222823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-2472694978688833528646107135200000000000000)
      constant := (6082165543290916738296795279298581662187541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/6250000000000000000)
  centralHi := (29659090825394567869/20000000000000000000)
  directionLo := (156317133896750300929/100000000000000000000)
  directionHi := (15631713389675030093/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree011.table
  base := (3658891999605431241364531214151508876183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-25466852951718007878334493135100000000000000)
      constant := (49976804785836986759992613167274223760855949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree011.table
  base := (170519116870719433158978982441645081479/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-290104139782463434471537765764000000000000)
      constant := (554352569053456174024968237477812571284586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156317133896750300929/100000000000000000000)
  centralHi := (15631713389675030093/10000000000000000000)
  directionLo := (32789358630302007243/20000000000000000000)
  directionHi := (20493349143938754527/12500000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree012.table
  base := (1000456369706306043787988799387059591037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-4877259974767252518612625764000000000000000)
      constant := (8110888983277744650687749493205741996287237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree012.table
  base := (894574574516502218581955308903324471229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-1664693908480217580392324090040000000000000)
      constant := (2740867291070968107759796546899182316555543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32789358630302007243/20000000000000000000)
  centralHi := (20493349143938754527/12500000000000000000)
  directionLo := (85618420359805567813/50000000000000000000)
  directionHi := (171236840719611135627/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree013.table
  base := (602955384058466363258256780051807845123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-33060266745489022345017016032900000000000000)
      constant := (50995793991184522852193720397994256615494769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree013.table
  base := (52611298752748268054128590787382590989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-1878867118048117988426959351260000000000000)
      constant := (2912024595349724839763157636230642825549852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/50000000000000000000)
  centralHi := (171236840719611135627/100000000000000000000)
  directionLo := (4455723864775153631/2500000000000000000)
  directionHi := (178228954591006145241/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree014.table
  base := (-593989921515085669394079278805049134071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-36856973642374529578358277481800000000000000)
      constant := (56507731161372955410098372452484201606843987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree014.table
  base := (-751482842486034522567110709710678786989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-4186080655232036792923189224960000000000000)
      constant := (6520973437421093809620492169720841491680537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/2500000000000000000)
  centralHi := (178228954591006145241/100000000000000000000)
  directionLo := (92478463559864015899/50000000000000000000)
  directionHi := (184956927119728031799/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree015.table
  base := (-1631382836759487283759308007121042218987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-13551226846420012270566512976900000000000000)
      constant := (21625878562510717905223251447228169188414813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree015.table
  base := (-1768141975851109990167001531242486943993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-4614427074367837608992459747400000000000000)
      constant := (7537678694785703152173585625412763819558069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92478463559864015899/50000000000000000000)
  centralHi := (184956927119728031799/100000000000000000000)
  directionLo := (191448608050677252451/100000000000000000000)
  directionHi := (47862152012669313113/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree016.table
  base := (-2539279722933225633310281741820128994053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-44450387436145544045040800379600000000000000)
      constant := (75870977782762142510359199280577533459404441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree016.table
  base := (-1329139350284994300512166473830868175377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-2521386746751819212530865134920000000000000)
      constant := (4424427883566298447050689547508637291948141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191448608050677252451/100000000000000000000)
  centralHi := (47862152012669313113/25000000000000000000)
  directionLo := (1581818177354376953/800000000000000000)
  directionHi := (98863636084648559563/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree017.table
  base := (-835026204541407605679763617198776148941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6600)
      previous := (4875)
      next := (0)
      square := (131424469507575250384889819385000000000000)
      linear := (-1419032186265619155246531230250000000000000)
      constant := (2626846503439404767900313824036523495272162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree017.table
  base := (-172186441389057815370104589445389276331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51000000000000000000000000000000000000000
      center := (145)
      previous := (110)
      next := (0)
      square := (2920543766835005564108662653000000000000)
      linear := (-32183058309643760241947063484000000000000)
      constant := (61385723565910045381128605864570293814238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1581818177354376953/800000000000000000)
  centralHi := (98863636084648559563/50000000000000000000)
  directionLo := (203812607054815809951/100000000000000000000)
  directionHi := (6369143970462994061/3125000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree018.table
  base := (-4051009316303638332233308204451908985259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-17347933743305519503907774425800000000000000)
      constant := (35023071641492455198150501259220584729341341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree018.table
  base := (-517654022828560570655741947777469105117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-2949733165887620028600135657360000000000000)
      constant := (6141658491801149530970076127587737143454244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203812607054815809951/100000000000000000000)
  centralHi := (6369143970462994061/3125000000000000000)
  directionLo := (2097214424646421591/1000000000000000000)
  directionHi := (209721442464642159101/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree019.table
  base := (-4685382730729668875538521152732949128651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-55840508126802065745064584726300000000000000)
      constant := (123035800832451933502593914136474797949136247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree019.table
  base := (-952775876028105445799010616671033675953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-1265562550182208174653908367432000000000000)
      constant := (2876147627219122948749494043674213802948749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2097214424646421591/1000000000000000000)
  centralHi := (209721442464642159101/100000000000000000000)
  directionLo := (1683346089390485227/781250000000000000)
  directionHi := (215468299441982109057/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree020.table
  base := (-1050769712550238195012297790764777557861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (44880)
      previous := (33150)
      next := (0)
      square := (893686392651511702617250771818000000000000)
      linear := (-11927443004737514595681169235040000000000000)
      constant := (28625928732032257166268322942662440716010617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree020.table
  base := (-266103327001322169369975876225946702813/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-675615917004684168933881235960000000000000)
      constant := (1671882302789681383026750339424208417322258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1683346089390485227/781250000000000000)
  centralHi := (215468299441982109057/100000000000000000000)
  directionLo := (110532905394037666001/50000000000000000000)
  directionHi := (221065810788075332003/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree021.table
  base := (-1441235202195285860691326145987803959859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-10572320320095513368624517937350000000000000)
      constant := (27547358772265876838491098502446443800813482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree021.table
  base := (-5824146398240298207322928732331423691323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-7184505589182642505408082882040000000000000)
      constant := (19290329836933721821829510733108655659622959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/50000000000000000000)
  centralHi := (221065810788075332003/100000000000000000000)
  directionLo := (9061001916729392683/4000000000000000000)
  directionHi := (56631261979558704269/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree022.table
  base := (-6225578633332931733493051619581484188413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-67230628817458587445088369073000000000000000)
      constant := (189445337512055756337268261893405678877813361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree022.table
  base := (-6276887524579536200503055615536153065009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-7612852008318443321477353404480000000000000)
      constant := (22089390213191954326756846591090155292637197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9061001916729392683/4000000000000000000)
  centralHi := (56631261979558704269/25000000000000000000)
  directionLo := (231855778382441950787/100000000000000000000)
  directionHi := (57963944595610487697/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree023.table
  base := (-1660352514056816573925518439874481815423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-35513667857172047339214815260950000000000000)
      constant := (107784563398440884060496987233943836788508662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree023.table
  base := (-6685808740432640739758771426294129352029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-8041198427454244137546623926920000000000000)
      constant := (25111219338527696260815547858562989851790857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/100000000000000000000)
  centralHi := (57963944595610487697/25000000000000000000)
  directionLo := (118533335611018612321/50000000000000000000)
  directionHi := (237066671222037224643/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree024.table
  base := (-701706808636394563432258212638961516739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-2494134753707653397059029732360000000000000)
      constant := (8120645637320938954938443044926061094961861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree024.table
  base := (-3527714868507206115944555552922664440279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-4234772423295022476807947224680000000000000)
      constant := (14175949320328857835655425620736049930278107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/50000000000000000000)
  centralHi := (237066671222037224643/100000000000000000000)
  directionLo := (242165462523595524813/100000000000000000000)
  directionHi := (121082731261797762407/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree025.table
  base := (-3678183222838878285459714247247360566367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-39310374754057554572556076709850000000000000)
      constant := (136783153004018908175037837069353845500638299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree025.table
  base := (-1847365875950387127319180310512256319901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-4448945632862922884842582485900000000000000)
      constant := (15904104478852857768783501074071747541291666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242165462523595524813/100000000000000000000)
  centralHi := (121082731261797762407/50000000000000000000)
  directionLo := (247159090211621398907/100000000000000000000)
  directionHi := (61789772552905349727/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree026.table
  base := (-15324904507427144801102265508936033879/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560600000000000000000000000000000000000000
      center := (4488)
      previous := (3315)
      next := (0)
      square := (89368639265151170261725077181800000000000)
      linear := (-1648349128100012327569068297372000000000000)
      constant := (6107707609766041298108389842677721276421630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree026.table
  base := (-3845483497112011700482899976420082704131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-4663118842430823292877217747120000000000000)
      constant := (17738749955523954274901340405163788295518423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247159090211621398907/100000000000000000000)
  centralHi := (61789772552905349727/25000000000000000000)
  directionLo := (50410760958035878867/20000000000000000000)
  directionHi := (7876681399693106073/3125000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree027.table
  base := (-317517084078895852974876947815800780451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1040400000000000000000000000000000000000000
      center := (2992)
      previous := (2210)
      next := (0)
      square := (59579092843434113507816718121200000000000)
      linear := (-1149522177358481648157262350900000000000000)
      constant := (4520750564559181151141043974561102170046949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree027.table
  base := (-1990615223122945532432450754536468354791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-4877292051998723700911853008340000000000000)
      constant := (19678793033737136099936650533413763872792406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50410760958035878867/20000000000000000000)
  centralHi := (7876681399693106073/3125000000000000000)
  directionLo := (256855261079416703439/100000000000000000000)
  directionHi := (3210690763492708793/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree028.table
  base := (-409247213664388951055438400107177584643/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-9001087019877163084513593776640000000000000)
      constant := (37456223950299718469444557097127386614061342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree028.table
  base := (-8206025907935330959173508852107966507629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-10182930523133248217892976539120000000000000)
      constant := (43446663451995257557233520032582393037885657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256855261079416703439/100000000000000000000)
  centralHi := (3210690763492708793/1250000000000000000)
  directionLo := (261568594787571494071/100000000000000000000)
  directionHi := (32696074348446436759/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree029.table
  base := (-8405287540540943690553474764896877000343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-93807577095657138078477199215300000000000000)
      constant := (411889303191685675354045824440759668766323571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree029.table
  base := (-8423380846643873264472354195665532746337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-10611276942269049033962247061560000000000000)
      constant := (47743241859731525295606234053197983108925821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568594787571494071/100000000000000000000)
  centralHi := (32696074348446436759/12500000000000000000)
  directionLo := (266198486874201126759/100000000000000000000)
  directionHi := (6654962171855028169/2500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree030.table
  base := (-8600435474554355957889792103202741557517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-32534761330847548437272820221400000000000000)
      constant := (150341982039958786347023423974569669208898283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree030.table
  base := (-430797314582659249348540271210407591279/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-1103962336140484985003151758400000000000000)
      constant := (5224608964519105767384579078121153236722214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266198486874201126759/100000000000000000000)
  centralHi := (6654962171855028169/2500000000000000000)
  directionLo := (135374609001359340733/50000000000000000000)
  directionHi := (270749218002718681467/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree031.table
  base := (-877161418668335688088605116994493804747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-10140099088942815254515972211310000000000000)
      constant := (49196260094066350948175262543416964841559159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree031.table
  base := (-8784896768249830593028681171047792153087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-11467969780540650666100788106440000000000000)
      constant := (56954188494950403299618227461541564203273571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135374609001359340733/50000000000000000000)
  centralHi := (270749218002718681467/100000000000000000000)
  directionLo := (275224714885951225239/100000000000000000000)
  directionHi := (6880617872148780631/2500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree032.table
  base := (-8919840739588346183878508125118074501613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-105197697786313659778500983562000000000000000)
      constant := (534691331514108027627097078155703664663913761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree032.table
  base := (-8931203606477441229716667445050629385731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-11896316199676451482170058628880000000000000)
      constant := (61866696265861733968413259324501104322571223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275224714885951225239/100000000000000000000)
  centralHi := (6880617872148780631/2500000000000000000)
  directionLo := (139814294976428106067/50000000000000000000)
  directionHi := (55925717990571242427/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree033.table
  base := (-2261489741814360334827485808440561165721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-18165734113866527835307040835150000000000000)
      constant := (96534258900600105473272102613367200815919358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree033.table
  base := (-9055670234964964689168190777918020811621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-12324662618812252298239329151320000000000000)
      constant := (66982916385303751944451205567105075956324593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139814294976428106067/50000000000000000000)
  centralHi := (55925717990571242427/20000000000000000000)
  directionLo := (141982087738200319733/50000000000000000000)
  directionHi := (283964175476400639467/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree034.table
  base := (-571916817757559400621445886941586250069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6600)
      previous := (4875)
      next := (0)
      square := (131424469507575250384889819385000000000000)
      linear := (-3317385634708372771917161954700000000000000)
      constant := (18397053024586518567812390695650495289746632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree034.table
  base := (-1831792257170986199011756104185456439647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102000000000000000000000000000000000000000
      center := (290)
      previous := (220)
      next := (0)
      square := (5841087533670011128217325306000000000000)
      linear := (-150035400446447683697748231456000000000000)
      constant := (850614971967163337614180967550541721578003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141982087738200319733/50000000000000000000)
  centralHi := (283964175476400639467/100000000000000000000)
  directionLo := (14411727653976943521/5000000000000000000)
  directionHi := (288234553079538870421/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree035.table
  base := (-9234552190768544864872198096805421060947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-116587818476970181478524767908700000000000000)
      constant := (673569545483229816551721686341877299461430559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree035.table
  base := (-9241626620973505200063949832985792405419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-13181355457083853930377870196200000000000000)
      constant := (77824288231373844126006119439801317984501727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14411727653976943521/5000000000000000000)
  centralHi := (288234553079538870421/100000000000000000000)
  directionLo := (58488515872410702407/20000000000000000000)
  directionHi := (73110644840513378009/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree036.table
  base := (-4649045286830484509906050280342856648831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-20064087562309281451977671559600000000000000)
      constant := (120568503010702000113734991182828229856390569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree036.table
  base := (-9304121179765637584239250056066951806863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-13609701876219654746447140718640000000000000)
      constant := (83548568795299861338045254147629952783449779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58488515872410702407/20000000000000000000)
  centralHi := (73110644840513378009/25000000000000000000)
  directionLo := (9268465882935802459/3125000000000000000)
  directionHi := (296590908253945678689/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree037.table
  base := (-9341684531041971952643717397575427863587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-124181232270741195945207290806500000000000000)
      constant := (775021097051692209642981591933968936380430639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree037.table
  base := (-4673410691897149809034101571959551246763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-7019024147677727781258205620540000000000000)
      constant := (44737393975745919534206786415691069069056479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/3125000000000000000)
  centralHi := (296590908253945678689/100000000000000000000)
  directionLo := (150341005296184812283/50000000000000000000)
  directionHi := (300682010592369624567/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree038.table
  base := (-9365666325483216017221333836633626835471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-127977939167626703178548552255400000000000000)
      constant := (828397189800823762086311633209747809802819787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree038.table
  base := (-2342509674974033755256259598212473831839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-7233197357245628189292840881760000000000000)
      constant := (47801337829101203606163459345579570375591174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150341005296184812283/50000000000000000000)
  centralHi := (300682010592369624567/100000000000000000000)
  directionLo := (60943638266463657297/20000000000000000000)
  directionHi := (152359095666159143243/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree039.table
  base := (-4685155878603957786741941886142377058129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-21962441010752035068648302284050000000000000)
      constant := (147256190707077486060299428291018677271806471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree039.table
  base := (-9374030856808779989721025133604792571551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-14894741133627057194654952285960000000000000)
      constant := (101932008464616035187323321217204644840465283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60943638266463657297/20000000000000000000)
  centralHi := (152359095666159143243/50000000000000000000)
  directionLo := (308701604731508954121/100000000000000000000)
  directionHi := (154350802365754477061/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree040.table
  base := (-584740610369032516218421440433053662919/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-67785676480698858822615537576600000000000000)
      constant := (470219586980113349971813939922407058145944344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree040.table
  base := (-2339752780691804844591049076059134570621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-7661543776381429005362111404200000000000000)
      constant := (54231300733586495562402207926113460654543186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308701604731508954121/100000000000000000000)
  centralHi := (154350802365754477061/50000000000000000000)
  directionLo := (312634267793500601859/100000000000000000000)
  directionHi := (15631713389675030093/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree041.table
  base := (-582654399877007677890415245079838762349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-69684029929141612439286168301050000000000000)
      constant := (499550898010794405969874636837761145099126024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree041.table
  base := (-4662577990072111438495398456707673682233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-7875716985949329413396746665420000000000000)
      constant := (57597150827828041851754389086854446917503989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312634267793500601859/100000000000000000000)
  centralHi := (15631713389675030093/5000000000000000000)
  directionLo := (39564759025897123149/12500000000000000000)
  directionHi := (316518072207176985193/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree042.table
  base := (-7416265134820521585537624148730353193/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520200000000000000000000000000000000000000
      center := (1496)
      previous := (1105)
      next := (0)
      square := (29789546421717056753908359060600000000000)
      linear := (-954431778367791547412757320340000000000000)
      constant := (7063491862578426694055954282268808783625175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree042.table
  base := (-2318152868646425704911943708090551890849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-8089890195517229821431381926640000000000000)
      constant := (61063491204245153464908852188650983021267834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39564759025897123149/12500000000000000000)
  centralHi := (316518072207176985193/100000000000000000000)
  directionLo := (20022174686448932451/6250000000000000000)
  directionHi := (320354794983182919217/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree043.table
  base := (-919956379793466146362439531996686113823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-14696147365205423934525485949990000000000000)
      constant := (112170410209255410817076092622154858253839131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree043.table
  base := (-4600749233927239722196964579706372609479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-8304063405085130229466017187860000000000000)
      constant := (64630269469263647828667107822374574947581707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20022174686448932451/6250000000000000000)
  centralHi := (320354794983182919217/100000000000000000000)
  directionLo := (162073053978511968017/50000000000000000000)
  directionHi := (64829221591404787207/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree044.table
  base := (-2277569066622932671534024984503697394749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-75379090274469873289298060474400000000000000)
      constant := (592820957858477153554682932721835298457547106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree044.table
  base := (-4555958491918529654637060141460971771413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-8518236614653030637500652449080000000000000)
      constant := (68297442262528724350116709009673337474184929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162073053978511968017/50000000000000000000)
  centralHi := (64829221591404787207/20000000000000000000)
  directionLo := (327893586303020072431/100000000000000000000)
  directionHi := (20493349143938754527/6250000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree045.table
  base := (-9002559093903827987691479728882720455647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-51518295815275084603979127465900000000000000)
      constant := (417112171961813708993655146208926044094862153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree045.table
  base := (-9003949804358245499664457130517777948109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-17464819648441862091070575420600000000000000)
      constant := (144129947396238661783494225060841086518989497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327893586303020072431/100000000000000000000)
  centralHi := (20493349143938754527/6250000000000000000)
  directionLo := (331598716182112998003/100000000000000000000)
  directionHi := (82899679045528249501/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree046.table
  base := (-8876487226581942726661307434990976710711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-158351594342710761045278643846600000000000000)
      constant := (1318787317791169617822192506061765408726322067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree046.table
  base := (-8877665444350655129259721220226640898469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-17893166067577662907139845943040000000000000)
      constant := (151865668149624355869543261193103502341027377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331598716182112998003/100000000000000000000)
  centralHi := (82899679045528249501/25000000000000000000)
  directionLo := (335262901628848557627/100000000000000000000)
  directionHi := (83815725407212139407/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree047.table
  base := (-218303072289667570151879756447282364621/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-16214830123959626827861990529550000000000000)
      constant := (138799383587638570010570704275492422835449348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree047.table
  base := (-8733120613533193610701937811678399930633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-18321512486713463723209116465480000000000000)
      constant := (159801997617888239965619890516034827260141189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335262901628848557627/100000000000000000000)
  centralHi := (83815725407212139407/25000000000000000000)
  directionLo := (67777494153609556717/20000000000000000000)
  directionHi := (169443735384023891793/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree048.table
  base := (-4284758878982796651457800373524233398953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-27657501356080295918660194457400000000000000)
      constant := (243159277827918641295969135900463468929323247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree048.table
  base := (-857036225324001877460102844900695536487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-1874985890584926453927838698792000000000000)
      constant := (16793889510289359923258531105087096969865771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67777494153609556717/20000000000000000000)
  centralHi := (169443735384023891793/50000000000000000000)
  directionLo := (85618420359805567813/25000000000000000000)
  directionHi := (342473681439222271253/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree049.table
  base := (-8388714730729515248504568000911425697417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-169741715033367282745302428193300000000000000)
      constant := (1531672476276748000085110030950138145283055149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree049.table
  base := (-4194714610866425416889171075620285119269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-9589102662492532677673828755180000000000000)
      constant := (88138163457263761122961706599057212801593777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/25000000000000000000)
  centralHi := (342473681439222271253/100000000000000000000)
  directionLo := (346022726296269958469/100000000000000000000)
  directionHi := (34602272629626995847/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree050.table
  base := (-2047437359979469513806904479432205691127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-86769210965126394989321844821100000000000000)
      constant := (803071992891448322694374215406480997984272038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree050.table
  base := (-1023794211083472014420517785465701509187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-9803275872060433085708464016400000000000000)
      constant := (92407132580849091080006129310004947166139484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346022726296269958469/100000000000000000000)
  centralHi := (34602272629626995847/10000000000000000000)
  directionLo := (21845983590066891573/6250000000000000000)
  directionHi := (349535737441070265169/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree051.table
  base := (-7972651476582219662336521699423737456667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4400)
      previous := (3250)
      next := (0)
      square := (87616313005050166923259879590000000000000)
      linear := (-3477159388767417592391861786100000000000000)
      constant := (32987646364450639865622518515738168169129949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree051.table
  base := (-7973162288913907927765505015131125990367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1450)
      previous := (1100)
      next := (0)
      square := (29205437668350055641086626530000000000000)
      linear := (-1178523421368039234558011679720000000000000)
      constant := (11385452161880826925674288957548312574491283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21845983590066891573/6250000000000000000)
  centralHi := (349535737441070265169/100000000000000000000)
  directionLo := (7060275812840239623/2000000000000000000)
  directionHi := (353013790642011981151/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree052.table
  base := (-3868722709353157424822661126339408397497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-90565917862011902222663106270000000000000000)
      constant := (880175110453499284376110547309173596274330909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree052.table
  base := (-96723463465707015621969892915616462699/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-2046324458239246780355546907768000000000000)
      constant := (20249157256385628088867730950993284214719736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7060275812840239623/2000000000000000000)
  centralHi := (353013790642011981151/100000000000000000000)
  directionLo := (4455723864775153631/1250000000000000000)
  directionHi := (356457909182012290481/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree053.table
  base := (-7484151682767702669769594471763533834783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-184928542620909311678667473988900000000000000)
      constant := (1840084595433170214977607050860079145487188251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree053.table
  base := (-3742258159174529484353029202148965870131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-10445795500764134309812369800060000000000000)
      constant := (105815453380945210336654712905916846590596423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4455723864775153631/1250000000000000000)
  centralHi := (356457909182012290481/100000000000000000000)
  directionLo := (71973813475008027583/20000000000000000000)
  directionHi := (89967266843760034479/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree054.table
  base := (-180319680764404759087871795675365761301/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-6290841650593160630400291181260000000000000)
      constant := (64052431860416521530763357845293494619424396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree054.table
  base := (-901636892543290138340929999412389500097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-10659968710332034717847005061280000000000000)
      constant := (110485338114983080715592113073957833213663604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71973813475008027583/20000000000000000000)
  centralHi := (89967266843760034479/25000000000000000000)
  directionLo := (18162409689269664361/5000000000000000000)
  directionHi := (363248193785393287221/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree055.table
  base := (-6923366155987475348715777033978096434119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-192521956414680326145349996886700000000000000)
      constant := (2004815192070618854636738587065118913524569443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree055.table
  base := (-865453259468275507190628229932784855929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-10874141919899935125881640322500000000000000)
      constant := (115255435051203930834480479203093102119638228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18162409689269664361/5000000000000000000)
  centralHi := (363248193785393287221/100000000000000000000)
  directionLo := (22912260886242088697/6250000000000000000)
  directionHi := (366596174179873419153/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree056.table
  base := (-3307950085954497190372785121608755624707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-98159331655782916689345629167800000000000000)
      constant := (1044905606405861556058471528512086879860411279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree056.table
  base := (-1323223901780871532060421804699761070989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-4435326051787134213566510233488000000000000)
      constant := (48050295875195834595210073496093307151452537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22912260886242088697/6250000000000000000)
  centralHi := (366596174179873419153/100000000000000000000)
  directionLo := (369913854239456063597/100000000000000000000)
  directionHi := (184956927119728031799/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree057.table
  base := (-6290399014544807325572194295400295587833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-66705123402817113537344173261500000000000000)
      constant := (725520314021402713076455429083413831176046367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree057.table
  base := (-3145292023164461527275652471945180330323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-11302488339035735941950910844940000000000000)
      constant := (125096248294418768492256177911003528653609959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369913854239456063597/100000000000000000000)
  centralHi := (184956927119728031799/50000000000000000000)
  directionLo := (373202042053977784699/100000000000000000000)
  directionHi := (3732020420539777847/1000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree058.table
  base := (-2973435389472950377263227769803099311201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-101956038552668423922686890616700000000000000)
      constant := (1132532158331195543878956997900726416074698597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree058.table
  base := (-5947026823081738786552861587537828019371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-23033323097207272699971092212320000000000000)
      constant := (260333915554884339674721948426164703107205343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373202042053977784699/100000000000000000000)
  centralHi := (3732020420539777847/1000000000000000000)
  directionLo := (376461510420691558829/100000000000000000000)
  directionHi := (37646151042069155883/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree059.table
  base := (-5585322197541467949044390083632256406459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-207708784002222355078715042682300000000000000)
      constant := (2355321284073126962527540792928667503260400423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree059.table
  base := (-1117090751262556695120600533071682290247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-4692333903268614703208072546952000000000000)
      constant := (54135146228790109916749863867114851454355851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376461510420691558829/100000000000000000000)
  centralHi := (37646151042069155883/10000000000000000000)
  directionLo := (94923249741303472233/25000000000000000000)
  directionHi := (379692998965213888933/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree060.table
  base := (-5205758871342259837584672001445792518691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-70501830299702620770685434710400000000000000)
      constant := (815777266863909624681161214944239493658884709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree060.table
  base := (-5205869755051566074862547523798379139457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-23890015935478874332109633257200000000000000)
      constant := (281217939099907582449204038176866805286090781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94923249741303472233/25000000000000000000)
  centralHi := (379692998965213888933/100000000000000000000)
  directionLo := (382897216101354504903/100000000000000000000)
  directionHi := (47862152012669313113/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree061.table
  base := (-240409273092996589116485661346962721317/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-21530219779599336954539756558010000000000000)
      constant := (254109582984442137551463319119344299771126898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree061.table
  base := (-4808278893804577537274112937133061374497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-24318362354614675148178903779640000000000000)
      constant := (291960535890158310614884856206745635788311101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382897216101354504903/100000000000000000000)
  centralHi := (47862152012669313113/12500000000000000000)
  directionLo := (77214968168907983489/20000000000000000000)
  directionHi := (193037420422269958723/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree062.table
  base := (-4392605850419103797688558297508988092973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-219098904692878876778738827029000000000000000)
      constant := (2636613341545228456968555657485537365910531681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree062.table
  base := (-2196342278102531220700310501594155959039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-12373354386875237982124087151040000000000000)
      constant := (151451759290546355515588859983197866783513187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77214968168907983489/20000000000000000000)
  centralHi := (193037420422269958723/50000000000000000000)
  directionLo := (97306631122995121109/25000000000000000000)
  directionHi := (389226524491980484437/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree063.table
  base := (-791804654080804487096394217747037847241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (14960)
      previous := (11050)
      next := (0)
      square := (297895464217170567539083590606000000000000)
      linear := (-14859707439317625600805339231860000000000000)
      constant := (182258954030936856170759574879189954559326159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree063.table
  base := (-3959089553883359850406895738837580243147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-25175055192886276780317444824520000000000000)
      constant := (314046884735027279730318727033187817929191551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97306631122995121109/25000000000000000000)
  centralHi := (389226524491980484437/100000000000000000000)
  directionLo := (392352892181357241107/100000000000000000000)
  directionHi := (98088223045339310277/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree064.table
  base := (-350744041703976535195626924169808351231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-22669231848664989124542134992680000000000000)
      constant := (283290871557005325134145707174702985435344507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree064.table
  base := (-3507496224834096720691990583921378766173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-25603401612022077596386715346960000000000000)
      constant := (325390632324920675141109898074780164609728009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392352892181357241107/100000000000000000000)
  centralHi := (98088223045339310277/25000000000000000000)
  directionLo := (395454544338594238251/100000000000000000000)
  directionHi := (98863636084648559563/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree065.table
  base := (-6075719077052163532686497068044104837/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560600000000000000000000000000000000000000
      center := (4488)
      previous := (3315)
      next := (0)
      square := (89368639265151170261725077181800000000000)
      linear := (-4609780507670707969575252227514000000000000)
      constant := (58673730786410540803021606014205518499568890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree065.table
  base := (-759476628704622064298319620650597874607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-13015874015578939206227992934700000000000000)
      constant := (168467379831898961840435265374291863285431462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395454544338594238251/100000000000000000000)
  centralHi := (98863636084648559563/25000000000000000000)
  directionLo := (24908253626513310543/6250000000000000000)
  directionHi := (398532058024212968689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree066.table
  base := (-2550282511693002816195363487014496638363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-78095244093473635237367957608200000000000000)
      constant := (1012072589023523158674647169149275294243617837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree066.table
  base := (-2550322044729342070934902893984569988999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-26460094450293679228525256391840000000000000)
      constant := (348679265346344961150842692675555377819537867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24908253626513310543/6250000000000000000)
  centralHi := (398532058024212968689/100000000000000000000)
  directionLo := (200792994093409611593/50000000000000000000)
  directionHi := (401585988186819223187/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree067.table
  base := (-127794431550543698023870560280174817693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-119041219588653206472722567136750000000000000)
      constant := (1570251193291492011623229714038695367180332168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree067.table
  base := (-2044744166341095601705183485725119959529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-26888440869429480044594526914280000000000000)
      constant := (360624148200573350290729910703836320995088357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200792994093409611593/50000000000000000000)
  centralHi := (401585988186819223187/100000000000000000000)
  directionLo := (80923373766286725391/20000000000000000000)
  directionHi := (101154217207858406739/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree068.table
  base := (-760573014861480904166901439178314977783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6600)
      previous := (4875)
      next := (0)
      square := (131424469507575250384889819385000000000000)
      linear := (-7114092531593880005258423403600000000000000)
      constant := (95486481988864904787038737597417153425197603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree068.table
  base := (-304234801689830216168149344542433437181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102000000000000000000000000000000000000000
      center := (290)
      previous := (220)
      next := (0)
      square := (5841087533670011128217325306000000000000)
      linear := (-321373968100768010125456440432000000000000)
      constant := (4385522438209617380776039172804335894703769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80923373766286725391/20000000000000000000)
  centralHi := (101154217207858406739/25000000000000000000)
  directionLo := (407625214109631619903/100000000000000000000)
  directionHi := (6369143970462994061/1562500000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree069.table
  base := (-979588985158574615422418643354893890061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-81891950990359142470709219057100000000000000)
      constant := (1118110587204167937317259721072383920991951339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree069.table
  base := (-979612515056860069066060543193501622893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-27745133707701081676733067959160000000000000)
      constant := (385115041669626436573394835926691234092951769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407625214109631619903/100000000000000000000)
  centralHi := (6369143970462994061/1562500000000000000)
  directionLo := (102652879834448774359/25000000000000000000)
  directionHi := (410611519337795097437/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree070.table
  base := (-42004069265481778083548502281887394743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-24947255986796293464546891862020000000000000)
      constant := (346387650136550416749200799131194432658820371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree070.table
  base := (-420060476982298114052027373976394335499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-28173480126836882492802338481600000000000000)
      constant := (397661050780360956413193757014762466111122367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102652879834448774359/25000000000000000000)
  centralHi := (410611519337795097437/100000000000000000000)
  directionLo := (103394065487296565827/25000000000000000000)
  directionHi := (413576261949186263309/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree071.table
  base := (78749036794165888710359664547060234089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-126634633382424220939405090034550000000000000)
      constant := (1787587300419662704744400285129085711006596467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree071.table
  base := (157481441979843967155869355762262575933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-28601826545972683308871609004040000000000000)
      constant := (410407434004511039946981658819485881653333911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103394065487296565827/25000000000000000000)
  centralHi := (413576261949186263309/100000000000000000000)
  directionLo := (104129975596256440553/25000000000000000000)
  directionHi := (416519902385025762213/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree072.table
  base := (23532083185279751806650190394444861227/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-42844328943622324852025240253000000000000000)
      constant := (614704342491534270094031978499455217344822832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree072.table
  base := (753012683401867487460312244487519938751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-29030172965108484124940879526480000000000000)
      constant := (423354190857919872413045167153730679786897117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104129975596256440553/25000000000000000000)
  centralHi := (416519902385025762213/100000000000000000000)
  directionLo := (419442884929284318201/100000000000000000000)
  directionHi := (209721442464642159101/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree073.table
  base := (42704516334521022962779183188507827071/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-130431340279309728172746351483450000000000000)
      constant := (1901515429703064662534028467519343825194160208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree073.table
  base := (1366532776294910842230801035708711613289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-29458519384244284941010150048920000000000000)
      constant := (436501320932240110800169638295119452968721563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419442884929284318201/100000000000000000000)
  centralHi := (209721442464642159101/50000000000000000000)
  directionLo := (422345638491473357869/100000000000000000000)
  directionHi := (42234563849147335787/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree074.table
  base := (1998051191142913948242172224411897894221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-264659387455504963578833964415800000000000000)
      constant := (3919589010583476082351513204372086039268606463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree074.table
  base := (1998041322265912829470521374212043258847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-29886865803380085757079420571360000000000000)
      constant := (449848823882064971046223834197681841505420349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422345638491473357869/100000000000000000000)
  centralHi := (42234563849147335787/10000000000000000000)
  directionLo := (85045715468267949239/20000000000000000000)
  directionHi := (106307144335334936549/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree075.table
  base := (661886568291804186755259853894197013697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-44742682392065078468695870977450000000000000)
      constant := (672983417567711213869865641131832612865251794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree075.table
  base := (1323768991613782409481482207380365296533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-15157606111257943286574345546900000000000000)
      constant := (231698349707136378284405020846298776712094111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85045715468267949239/20000000000000000000)
  centralHi := (106307144335334936549/25000000000000000000)
  directionLo := (85618420359805567813/20000000000000000000)
  directionHi := (214046050899513919533/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree076.table
  base := (1657514716803870212672867158072019200981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-136126400624637989022758243656800000000000000)
      constant := (2078982670629586330321871507080435965825254743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree076.table
  base := (3315022471220955534304600860069611450791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-30743558641651687389217961616240000000000000)
      constant := (477144947279203091291286400879120353127835797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85618420359805567813/20000000000000000000)
  centralHi := (214046050899513919533/50000000000000000000)
  directionLo := (430936598883964218113/100000000000000000000)
  directionHi := (215468299441982109057/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree077.table
  base := (800100077281521320808317549793479128337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (44880)
      previous := (33150)
      next := (0)
      square := (893686392651511702617250771818000000000000)
      linear := (-55209901629232297055771549752500000000000000)
      constant := (855956703182018078526492152578488517638413611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree077.table
  base := (500061817498324422261805416151396870927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-15585952530393744102643616069340000000000000)
      constant := (245546783631674498866353127848993044348374836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430936598883964218113/100000000000000000000)
  centralHi := (215468299441982109057/50000000000000000000)
  directionLo := (433762442925442920127/100000000000000000000)
  directionHi := (6777538170710045627/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree078.table
  base := (4703958886486163695427560304925558329371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-93282071681015664170733003403800000000000000)
      constant := (1467785009148885384948890647492111377214693971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree078.table
  base := (587994247247796991960510218097153622813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-15800125739961644510678251330560000000000000)
      constant := (252621279591651733948784717306040928763915484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433762442925442920127/100000000000000000000)
  centralHi := (6777538170710045627/1562500000000000000)
  directionLo := (17462799845505534877/4000000000000000000)
  directionHi := (218284998068819185963/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree079.table
  base := (5425404722977843874494559275484780415923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-283642921939932499745540271660300000000000000)
      constant := (4528679874223485921547830602507857741585447169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree079.table
  base := (2712700301299519026195411790106901096119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-16014298949529544918712886591780000000000000)
      constant := (259795961440372137049383021600442683250335173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17462799845505534877/4000000000000000000)
  centralHi := (218284998068819185963/50000000000000000000)
  directionLo := (43935960916154666387/10000000000000000000)
  directionHi := (439359609161546663871/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree080.table
  base := (6164837713613092816583721954217823320283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-287439628836818006978881533109200000000000000)
      constant := (4655758054818330360340623637288761675368168249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree080.table
  base := (770604281920845193709388849817709272951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-16228472159097445326747521853000000000000000)
      constant := (267070829109139041120751142323167815758594068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43935960916154666387/10000000000000000000)
  centralHi := (439359609161546663871/100000000000000000000)
  directionLo := (110532905394037666001/25000000000000000000)
  directionHi := (88426324315230132801/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree081.table
  base := (6922257700047534416769780634705885794839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-97078778577901171404074264852700000000000000)
      constant := (1594863189331876101492773060968620008952376239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree081.table
  base := (6922254797982100845171813341942103438283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-32885290737330691469564314228440000000000000)
      constant := (548891765075995805005867591188303803680991361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/25000000000000000000)
  centralHi := (88426324315230132801/20000000000000000000)
  directionLo := (27805397648807407377/6250000000000000000)
  directionHi := (444886362380918518033/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree082.table
  base := (1539532908795693955191016487385768388153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (44880)
      previous := (33150)
      next := (0)
      square := (893686392651511702617250771818000000000000)
      linear := (-59006608526117804289112811201400000000000000)
      constant := (983034882535240758890251650787271150732757859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree082.table
  base := (120275970453343056771187857325460516263/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-16656818578233246142816792375440000000000000)
      constant := (281921121674308339213485933647317576563200672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27805397648807407377/6250000000000000000)
  centralHi := (444886362380918518033/100000000000000000000)
  directionLo := (447624150451576291789/100000000000000000000)
  directionHi := (44762415045157629179/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree083.table
  base := (8491058123915148431489677645949553331717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-298829749527474528678905317455900000000000000)
      constant := (5047512587912064504399383292754594364647387751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree083.table
  base := (849105608117164523605333884205886887631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-3374198357560229310170285527332000000000000)
      constant := (57899309294311968235683790769962503931576077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447624150451576291789/100000000000000000000)
  centralHi := (44762415045157629179/10000000000000000000)
  directionLo := (450345294970942117803/100000000000000000000)
  directionHi := (112586323742735529451/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree084.table
  base := (2325609583122985438044784092993456258563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-50437742737393339318707763150800000000000000)
      constant := (863600682144239405685580693821751959457044726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree084.table
  base := (9302436619038327009856969866742118666483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-34170329994738093917772125795760000000000000)
      constant := (594344313776778414223632024263905416883840761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450345294970942117803/100000000000000000000)
  centralHi := (112586323742735529451/25000000000000000000)
  directionLo := (453050095836469634151/100000000000000000000)
  directionHi := (56631261979558704269/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree085.table
  base := (5065902537116191738726318809819237655573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6600)
      previous := (4875)
      next := (0)
      square := (131424469507575250384889819385000000000000)
      linear := (-9012445980036633621929054128050000000000000)
      constant := (156395556670332844628303727889332030083908007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree085.table
  base := (5065901818594844782000478966089112779347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 255000000000000000000000000000000000000000
      center := (725)
      previous := (550)
      next := (0)
      square := (14602718834175027820543313265000000000000)
      linear := (-1017608129819820433348276362300000000000000)
      constant := (17938114875750882236810592099770544751746697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453050095836469634151/100000000000000000000)
  centralHi := (56631261979558704269/12500000000000000000)
  directionLo := (45573884404602135727/10000000000000000000)
  directionHi := (455738844046021357271/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree086.table
  base := (686197391480479760232449464078178537351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-155109935109065525189464550901300000000000000)
      constant := (2727523544511474193846785276994116217015598824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree086.table
  base := (10979157058631661406626583035818852335951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-35027022833009695549910666840640000000000000)
      constant := (625647868872620567857180718842294944975269517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45573884404602135727/10000000000000000000)
  centralHi := (455738844046021357271/100000000000000000000)
  directionLo := (91682364412655334293/20000000000000000000)
  directionHi := (229205911031638335733/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree087.table
  base := (5922248911943119485631665198609399332111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-52336096185836092935378393875250000000000000)
      constant := (932399763159953699969152631354458047662820711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree087.table
  base := (5922248406751151095082095220121198294359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-17727684626072748182989968681540000000000000)
      constant := (320800101503739913679575447978425078921209253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91682364412655334293/20000000000000000000)
  centralHi := (229205911031638335733/50000000000000000000)
  directionLo := (461069304164073243837/100000000000000000000)
  directionHi := (230534652082036621919/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree088.table
  base := (12727823685041643446908478180097737790029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-317813284011902064845611624700400000000000000)
      constant := (5735503396057094652506225625351302647975596287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree088.table
  base := (6363911418996249170393992877305236084077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-17941857835640648591024603942760000000000000)
      constant := (328876454062392636544481849499503639684894759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461069304164073243837/100000000000000000000)
  centralHi := (230534652082036621919/50000000000000000000)
  directionLo := (231855778382441950787/50000000000000000000)
  directionHi := (18548462270595356063/4000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree089.table
  base := (1703641972934403077403168536854728838099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-160804995454393786039476443074650000000000000)
      constant := (2939180769909090561497718671632934796494745988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree089.table
  base := (3407283768361976975003313571934840004343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-18156031045208548999059239203980000000000000)
      constant := (337052992086841795284306440165755012567530762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231855778382441950787/50000000000000000000)
  centralHi := (18548462270595356063/4000000000000000000)
  directionLo := (93267767746908492437/20000000000000000000)
  directionHi := (233169419367271231093/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree090.table
  base := (7274217030358537993256177651643392509507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-54234449634278846552049024599700000000000000)
      constant := (1003828834964456821808295578449424463917227707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree090.table
  base := (1454843346562107249581309640970804372587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-3674040850955289881418774893040000000000000)
      constant := (69065943110714223338955111797521687391032929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93267767746908492437/20000000000000000000)
  centralHi := (233169419367271231093/50000000000000000000)
  directionLo := (468951401690250902789/100000000000000000000)
  directionHi := (46895140169025090279/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree091.table
  base := (7742859231377648555845646857829674493521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-164601702351279293272817704523550000000000000)
      constant := (3084668902770659608479356385103269950072944363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree091.table
  base := (15485717964047970503668519644250382637741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-37168754928688699630257019452840000000000000)
      constant := (707413248881408894803320445453205081746921447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468951401690250902789/100000000000000000000)
  centralHi := (46895140169025090279/10000000000000000000)
  directionLo := (471549490278825891/100000000000000000)
  directionHi := (471549490278825891001/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree092.table
  base := (3288197787881695181721827454460366247389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (44880)
      previous := (33150)
      next := (0)
      square := (893686392651511702617250771818000000000000)
      linear := (-66600022319888818755795334099200000000000000)
      constant := (1263491185338070084562800635578354237828376367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree092.table
  base := (4110247130381929360674886558428097495119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-18798550673912250223163144987640000000000000)
      constant := (362183718727780203982498961024794321056536346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471549490278825891/100000000000000000)
  centralHi := (471549490278825891001/100000000000000000000)
  directionLo := (118533335611018612321/25000000000000000000)
  directionHi := (94826668488814889857/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree093.table
  base := (17414245443800632237157864527380762777071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-112265606165443200337439310648300000000000000)
      constant := (2155775790956020425127460600803467363983161671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree093.table
  base := (17414245093687786988963025194306044592163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-38025447766960301262395560497720000000000000)
      constant := (741521996791125792551724835861423340661405321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118533335611018612321/25000000000000000000)
  centralHi := (94826668488814889857/20000000000000000000)
  directionLo := (95340637936225164711/20000000000000000000)
  directionHi := (119175797420281455889/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree094.table
  base := (18405487931921372800704008399195289985923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-340593525393215108245659193393800000000000000)
      constant := (6618952143731038675770217700123920847760157169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree094.table
  base := (9202743819310080327055536786259062349561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-19226897093048051039232415510080000000000000)
      constant := (379438463425885398267051786184006607057069387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95340637936225164711/20000000000000000000)
  centralHi := (119175797420281455889/25000000000000000000)
  directionLo := (95851851455697793851/20000000000000000000)
  directionHi := (59907407159811121157/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree095.table
  base := (9707358181128466067483450345140194389601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-172195116145050307739500227421350000000000000)
      constant := (3386165119477675356029864408543753936822056603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree095.table
  base := (4853679029144081342212714359960659714513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-19441070302615951447267050771300000000000000)
      constant := (388216113801516729540528622276671783944965542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95851851455697793851/20000000000000000000)
  centralHi := (59907407159811121157/12500000000000000000)
  directionLo := (60225220568568999929/12500000000000000000)
  directionHi := (481801764548551999433/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree096.table
  base := (817677227819208097296157687217855548341/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1040400000000000000000000000000000000000000
      center := (2992)
      previous := (2210)
      next := (0)
      square := (59579092843434113507816718121200000000000)
      linear := (-4642492522493148302831222883888000000000000)
      constant := (92366155443121706160382136687813642281234941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree096.table
  base := (817677219588444650971457333781875661859/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346800000000000000000000000000000000000000
      center := (986)
      previous := (748)
      next := (0)
      square := (19859697614478037835938906040400000000000)
      linear := (-1572419480974708148424134882601600000000000)
      constant := (31767515960484080890396922777790486198831753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60225220568568999929/12500000000000000000)
  centralHi := (481801764548551999433/100000000000000000000)
  directionLo := (484330925047191049627/100000000000000000000)
  directionHi := (121082731261797762407/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree097.table
  base := (10743565447094935252651598695236397615171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-175991823041935814972841488870250000000000000)
      constant := (3542173200637763989436647885537554610591179313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree097.table
  base := (21487130721867121712235424836666883863533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-39738833443503504526672642587480000000000000)
      constant := (812143941047628010163056926660150188309683111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484330925047191049627/100000000000000000000)
  centralHi := (121082731261797762407/25000000000000000000)
  directionLo := (121711736695777733711/25000000000000000000)
  directionHi := (97369389356622186969/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree098.table
  base := (22550316922690453444447623293484112939577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-355780352980757137179024239189400000000000000)
      constant := (7242984467801018909453014788816056533267519331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree098.table
  base := (4510063355678558113361977210136533713373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-8033435972527861068548382621984000000000000)
      constant := (166060070735913705594596793426820374729494391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121711736695777733711/25000000000000000000)
  centralHi := (97369389356622186969/20000000000000000000)
  directionLo := (97870006483499674247/20000000000000000000)
  directionHi := (122337508104374592809/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree099.table
  base := (2363148874680641365407483677826269330981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-11985901995921421480412183354610000000000000)
      constant := (246779195251464301130269447646401126529881581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree099.table
  base := (23631488625988559916711189281556612499639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-40595526281775106158811183632360000000000000)
      constant := (848657136879052854636938280646349583037187013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97870006483499674247/20000000000000000000)
  centralHi := (122337508104374592809/25000000000000000000)
  directionLo := (245920189727265054323/50000000000000000000)
  directionHi := (491840379454530108647/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree100.table
  base := (24730646333724687224500943109936730771517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-363373766774528151645706762087200000000000000)
      constant := (7565520570248218014551238262186836310210147151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree100.table
  base := (24730646232576295750560780696634378049857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-41023872700910906974880454154800000000000000)
      constant := (867214290618269247967054661023982005769226019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245920189727265054323/50000000000000000000)
  centralHi := (491840379454530108647/100000000000000000000)
  directionLo := (247159090211621398907/50000000000000000000)
  directionHi := (98863636084648559563/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree101.table
  base := (25847789651860917119734569080929673715807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-367170473671413658879048023536100000000000000)
      constant := (7729418605667433113430638602061744244004442021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree101.table
  base := (25847789567188146307569257022177339538873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-41452219120046707790949724677240000000000000)
      constant := (885971814870368580486728695628667753380202891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247159090211621398907/50000000000000000000)
  centralHi := (98863636084648559563/20000000000000000000)
  directionLo := (15524488220351204731/3125000000000000000)
  directionHi := (496783623051238551393/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree102.table
  base := (26982918670745477674460659626845965075201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4400)
      previous := (3250)
      next := (0)
      square := (87616313005050166923259879590000000000000)
      linear := (-7273866285652924825733123235000000000000000)
      constant := (154805293403212153754506491653907432656505753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree102.table
  base := (13491459299935787708767784815744696721927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 255000000000000000000000000000000000000000
      center := (725)
      previous := (550)
      next := (0)
      square := (14602718834175027820543313265000000000000)
      linear := (-1231781339387720841382911623520000000000000)
      constant := (26615579694393588333423413979442979532818277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15524488220351204731/3125000000000000000)
  centralHi := (496783623051238551393/100000000000000000000)
  directionLo := (499236890430669728157/100000000000000000000)
  directionHi := (249618445215334864079/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree103.table
  base := (14068016680463018512089277564164573985131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-187381943732592336672865273216950000000000000)
      constant := (4031237321853780826580058516019801170805977193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree103.table
  base := (5627206660321579201851022292896668635803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-8461782391663661884617653144424000000000000)
      constant := (184817594962030062965064481144013411707241201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499236890430669728157/100000000000000000000)
  centralHi := (249618445215334864079/50000000000000000000)
  directionLo := (250839080588459136031/50000000000000000000)
  directionHi := (501678161176918272063/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree104.table
  base := (29307133693883952251877679957417704975341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-378560594362070180579071807882800000000000000)
      constant := (8231632645876127577790062953507730351922585823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree104.table
  base := (14653566822121040788578237720482213185679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-21368629188727055119578768122280000000000000)
      constant := (471723305224131553486588638473578078831983693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250839080588459136031/50000000000000000000)
  centralHi := (501678161176918272063/100000000000000000000)
  directionLo := (50410760958035878867/10000000000000000000)
  directionHi := (504107609580358788671/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree105.table
  base := (15248109820981123623436736414036504542421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-63726216876492614635402178221950000000000000)
      constant := (1400423994975618371796332867839783948314837021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree105.table
  base := (15248109800211006129960285865054543128101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-21582802398294955527613403383500000000000000)
      constant := (481502808250003045930098519049502288892063567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50410760958035878867/10000000000000000000)
  centralHi := (504107609580358788671/100000000000000000000)
  directionLo := (506525405751570273757/100000000000000000000)
  directionHi := (253262702875785136879/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree106.table
  base := (31703291178303301325412027461674757352181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (224400)
      previous := (165750)
      next := (0)
      square := (4468431963257558513086253859090000000000000)
      linear := (-386154008155841195045754330780600000000000000)
      constant := (8575208615430739597928588061940448131619068343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree106.table
  base := (6340658228709125175164342437051232045899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-8718790243145142374259215457888000000000000)
      constant := (196552998588463056314965103510491418183794433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506525405751570273757/100000000000000000000)
  centralHi := (253262702875785136879/50000000000000000000)
  directionLo := (508931715760338870589/100000000000000000000)
  directionHi := (50893171576033887059/10000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree107.table
  base := (4116043534599336332987843470543765078759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-194975357526363351139547796114750000000000000)
      constant := (4374813291201730218073179048446236995638225908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree107.table
  base := (32928348247714704017004640565277157174661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-44022297634861512687365347811880000000000000)
      constant := (1002724739752736920757452208146455295270431087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508931715760338870589/100000000000000000000)
  centralHi := (50893171576033887059/10000000000000000000)
  directionLo := (511326701768773085213/100000000000000000000)
  directionHi := (255663350884386542607/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree108.table
  base := (17085695456010942711120263224845178570317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (37400)
      previous := (27625)
      next := (0)
      square := (744738660542926418847708976515000000000000)
      linear := (-65624570324935368252072808946400000000000000)
      constant := (1487632978428927194848161193289822309461394517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree108.table
  base := (6834278177538847685709491227870087211069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (4930)
      previous := (3740)
      next := (0)
      square := (99298488072390189179694530202000000000000)
      linear := (-8890128810799462700686923666864000000000000)
      constant := (204576971381878451450211964389475365611996823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511326701768773085213/100000000000000000000)
  centralHi := (255663350884386542607/50000000000000000000)
  directionLo := (256855261079416703439/50000000000000000000)
  directionHi := (513710522158833406879/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree109.table
  base := (17716209529613361057963448952761575540139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-198772064423248858372889057563650000000000000)
      constant := (4551861239873929923543436861654023573939704617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree109.table
  base := (35432419038876501082703396584949318250249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-44878990473133114319503888856760000000000000)
      constant := (1043245344390946390855591916021591058922965883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256855261079416703439/50000000000000000000)
  centralHi := (513710522158833406879/100000000000000000000)
  directionLo := (129020832913640037113/25000000000000000000)
  directionHi := (516083331654560148453/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree110.table
  base := (917785817356768770660361075580901112291/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-40134083574338322397911937657620000000000000)
      constant := (928340040973799814542565227629531085516826692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree110.table
  base := (9177858169312272242765957384227576364651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-22653668446134457567786579689600000000000000)
      constant := (531903101088290284081379103054250617416304834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129020832913640037113/25000000000000000000)
  centralHi := (516083331654560148453/100000000000000000000)
  directionLo := (2025176880622134509/390625000000000000)
  directionHi := (103689056287853286861/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree111.table
  base := (3800843179360270644042367434448878492659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-13504584754675624373748687934170000000000000)
      constant := (315494388678673584747546099268776532959406059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree111.table
  base := (38008431779366336945754359669343860086741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-45735683311404715951642429901640000000000000)
      constant := (1084567430245967397489351591460561126695204447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2025176880622134509/390625000000000000)
  centralHi := (103689056287853286861/20000000000000000000)
  directionLo := (520796519267947524671/100000000000000000000)
  directionHi := (8137445613561680073/1562500000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree112.table
  base := (19661708167114738722473435355348492008541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-204467124768577119222900949737000000000000000)
      constant := (4824008115717536394476533290205784283142645423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree112.table
  base := (9830854080580898326099944294673740397681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-23082014865270258383855850212040000000000000)
      constant := (552764514289624272904706382589044265849578854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520796519267947524671/100000000000000000000)
  centralHi := (8137445613561680073/1562500000000000000)
  directionLo := (261568594787571494071/50000000000000000000)
  directionHi := (523137189575142988143/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree113.table
  base := (325251090349520393294494990493383395967/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3121200000000000000000000000000000000000000
      center := (8976)
      previous := (6630)
      next := (0)
      square := (178737278530302340523450154363600000000000)
      linear := (-16509238257361589827165726436916000000000000)
      constant := (393318164911493223498877029281829353193652505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree113.table
  base := (40656386283733936839570535338382969632047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-46592376149676317583780970946520000000000000)
      constant := (1126690997157014552436100310249138034670984749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261568594787571494071/50000000000000000000)
  centralHi := (523137189575142988143/100000000000000000000)
  directionLo := (21018697343138981493/4000000000000000000)
  directionHi := (262733716789237268663/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree114.table
  base := (42007341650031984242329488054641028147747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-138842554443641750970828140790600000000000000)
      constant := (3339881778081895356450379546585121314212289947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree114.table
  base := (42007341641706983746610856456430841260177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-47020722568812118399850241468960000000000000)
      constant := (1148053335960286454610777667414765539372573459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21018697343138981493/4000000000000000000)
  centralHi := (262733716789237268663/50000000000000000000)
  directionLo := (527787389378069553261/100000000000000000000)
  directionHi := (263893694689034776631/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree115.table
  base := (21688141190895037356220862611732131274967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-210162185113905380072912841910350000000000000)
      constant := (5104044932821323108384565410744970820338567501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree115.table
  base := (43376282374829490574083880251414472315789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-47449068987947919215919511991400000000000000)
      constant := (1169616044970498970261049078810976347497789063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527787389378069553261/100000000000000000000)
  centralHi := (263893694689034776631/50000000000000000000)
  directionLo := (530097192052068374363/100000000000000000000)
  directionHi := (132524298013017093591/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree116.table
  base := (22381604233983429656988788035798781448591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-212060538562348133689583472634800000000000000)
      constant := (5199143858407183919764196946049337891643355573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree116.table
  base := (22381604231073753676269155228119888274479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-23938707703541860015994391256920000000000000)
      constant := (595689562084742512381700135287099943133973293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530097192052068374363/100000000000000000000)
  centralHi := (132524298013017093591/25000000000000000000)
  directionLo := (266198486874201126759/50000000000000000000)
  directionHi := (532396973748402253519/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree117.table
  base := (46168119888014749363639248370369187559743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-142639261340527258204169402239500000000000000)
      constant := (3530079629200172701044385059607080256842891543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree117.table
  base := (46168119883149874841358606123697797603093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-48305761826219520848058053036280000000000000)
      constant := (1213342573539461443056217568703205990521881631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266198486874201126759/50000000000000000000)
  centralHi := (532396973748402253519/100000000000000000000)
  directionLo := (534686863773018435721/100000000000000000000)
  directionHi := (267343431886509217861/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree118.table
  base := (5948877077727443442259157209012026288789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-215857245459233640922924734083700000000000000)
      constant := (5391971688922072962934643721256183364525682268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree118.table
  base := (11897754154438223222489885786704239097389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-24367054122677660832063661779360000000000000)
      constant := (617753196531507828554471791948625150594872526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534686863773018435721/100000000000000000000)
  centralHi := (267343431886509217861/50000000000000000000)
  directionLo := (536966988674719025937/100000000000000000000)
  directionHi := (268483494337359512969/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree119.table
  base := (9806379729937035658752211373004832029121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918000000000000000000000000000000000000000
      center := (2640)
      previous := (1950)
      next := (0)
      square := (52569787803030100153955927754000000000000)
      linear := (-5123661150768856342108126230780000000000000)
      constant := (129169425734018386238479005412459217901366539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree119.table
  base := (49031898646286014377045349555283483068523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1450)
      previous := (1100)
      next := (0)
      square := (29205437668350055641086626530000000000000)
      linear := (-2891909097911242498835093769480000000000000)
      constant := (73992387219005488386318522462239457636494673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536966988674719025937/100000000000000000000)
  centralHi := (268483494337359512969/50000000000000000000)
  directionLo := (134809368081692788671/25000000000000000000)
  directionHi := (107847494465354230937/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree120.table
  base := (5049076595231947720924601687448086483153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-14643596823741276543751066368840000000000000)
      constant := (372553743869741068578560438493052472942680953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree120.table
  base := (12622691487369610507228406998300176853183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-24795400541813461648132932301800000000000000)
      constant := (640217571251493299097665742039052506663419322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134809368081692788671/25000000000000000000)
  centralHi := (107847494465354230937/20000000000000000000)
  directionLo := (135374609001359340733/25000000000000000000)
  directionHi := (541498436005437362933/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree121.table
  base := (2598380925541045518073848418732621240737/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-44310461160912380354587325251410000000000000)
      constant := (1137557676379866493792601225246066287082941622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree121.table
  base := (51967618508446524418493394994839669658579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-50019147502762724112335135126040000000000000)
      constant := (1303200072386323418205422847892565993593987993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135374609001359340733/25000000000000000000)
  centralHi := (541498436005437362933/100000000000000000000)
  directionLo := (108749999693113415519/20000000000000000000)
  directionHi := (135937499616391769399/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree122.table
  base := (6682807038333264340094804791974196195209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-223450659253004655389607256981500000000000000)
      constant := (5788147265183161835128799488507598611644863308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree122.table
  base := (53462456304681863267894291251736744946121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-50447493921898524928404405648480000000000000)
      constant := (1326165372357056981290758031781015757868286907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108749999693113415519/20000000000000000000)
  centralHi := (135937499616391769399/25000000000000000000)
  directionLo := (545992276013382496487/100000000000000000000)
  directionHi := (68249034501672812061/12500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree123.table
  base := (2199011172867926685466945247800855406427/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1040400000000000000000000000000000000000000
      center := (2992)
      previous := (2210)
      next := (0)
      square := (59579092843434113507816718121200000000000)
      linear := (-6009307005371930906834077005492000000000000)
      constant := (157050208208713730440118280969040024912116627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree123.table
  base := (27487639660020028681246108846530281810963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (12325)
      previous := (9350)
      next := (0)
      square := (248246220180975472949236325505000000000000)
      linear := (-25437920170517162872236838085460000000000000)
      constant := (674665521199728045799128970924521754330104921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545992276013382496487/100000000000000000000)
  centralHi := (68249034501672812061/12500000000000000000)
  directionLo := (548225382576585112663/100000000000000000000)
  directionHi := (68528172822073139083/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree124.table
  base := (28253043769057751672041954670788191616919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-227247366149890162622948518430400000000000000)
      constant := (5991495009760688835109475875086160259186818957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree124.table
  base := (5650608753673001938421301099640514721127/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 867000000000000000000000000000000000000000
      center := (2465)
      previous := (1870)
      next := (0)
      square := (49649244036195094589847265101000000000000)
      linear := (-5130418676017012656054294669336000000000000)
      constant := (137269708249809587642315227849612326263217109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (548225382576585112663/100000000000000000000)
  centralHi := (68528172822073139083/12500000000000000000)
  directionLo := (550449429771902450479/100000000000000000000)
  directionHi := (6880617872148780631/1250000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree125.table
  base := (14513720234615355000919880121878785947137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (112200)
      previous := (82875)
      next := (0)
      square := (2234215981628779256543126929545000000000000)
      linear := (-229145719598332916239619149154850000000000000)
      constant := (6094483870916826337865603506197665333491020022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree125.table
  base := (72568601171629763948012449546484164791/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 173400000000000000000000000000000000000000
      center := (493)
      previous := (374)
      next := (0)
      square := (9929848807239018917969453020200000000000)
      linear := (-1034650663586118547532244344316000000000000)
      constant := (27925269852756979467360446856608828333980752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550449429771902450479/100000000000000000000)
  centralHi := (6880617872148780631/1250000000000000000)
  directionLo := (110532905394037666001/20000000000000000000)
  directionHi := (276332263485094165003/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree126.table
  base := (5962165950561410248744017549121243075713/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2601000000000000000000000000000000000000000
      center := (7480)
      previous := (5525)
      next := (0)
      square := (148947732108585283769541795303000000000000)
      linear := (-15402938203118377990419318658620000000000000)
      constant := (413223292748558442666773151439164353239929513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree126.table
  base := (59621659504646950491202023546713186179623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-52160879598441728192681487738240000000000000)
      constant := (1420030272803877126370773273112440332417733141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110532905394037666001/20000000000000000000)
  centralHi := (276332263485094165003/50000000000000000000)
  directionLo := (138717695339796023849/25000000000000000000)
  directionHi := (554870781359184095397/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree127.table
  base := (12241284644555425848590973184271541566827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (44880)
      previous := (33150)
      next := (0)
      square := (893686392651511702617250771818000000000000)
      linear := (-93176970598087369389184164241500000000000000)
      constant := (2521236628251923401132290248744320838845951081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree127.table
  base := (61206423221969149207941655929269112017651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-52589226017577529008750758260680000000000000)
      constant := (1443997422981623155583985646270236320119303417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138717695339796023849/25000000000000000000)
  centralHi := (554870781359184095397/100000000000000000000)
  directionLo := (557068298004042711107/100000000000000000000)
  directionHi := (139267074501010677777/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree128.table
  base := (196278662729595032454067344783902113457/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (22440)
      previous := (16575)
      next := (0)
      square := (446843196325755851308625385909000000000000)
      linear := (-46968155988732235417926208265640000000000000)
      constant := (1281742081811364971133393042462361222121759072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree128.table
  base := (62809172072795447400269113931719043712383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-53017572436713329824820028783120000000000000)
      constant := (1468164943156803270767111565250160410898636061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell023.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557068298004042711107/100000000000000000000)
  centralHi := (139267074501010677777/25000000000000000000)
  directionLo := (139814294976428106067/25000000000000000000)
  directionHi := (559257179905712424269/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree129.table
  base := (64429906041521523890024376009202061529371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (74800)
      previous := (55250)
      next := (0)
      square := (1489477321085852837695417953030000000000000)
      linear := (-157826088928069287137534448035100000000000000)
      constant := (4343470604297552662654601022393684562037893971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree129.table
  base := (64429906040957713424361717828985434540389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24650)
      previous := (18700)
      next := (0)
      square := (496492440361950945898472651010000000000000)
      linear := (-53445918855849130640889299305560000000000000)
      constant := (1492532833315399701784956766730570371746517263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell023.Kernel129
