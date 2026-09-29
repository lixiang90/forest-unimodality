import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell024.Parameters
import ForestUnimodality.BinomialMassData.Q22_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q67_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q67_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q67_153.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree000.table
  base := (2378739454914533562156719881/100000000000000000000000000)
  polynomial :=
    { denominator := 102000000000000000000000000000000000000000
      center := (319)
      previous := (242)
      next := (0)
      square := (6272529741726107263555256598000000000000)
      linear := (24080912909862332071941893040000000000000)
      constant := (2426314244012824233399854278620000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree000.table
  base := (2378739454914533562156719881/100000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (946)
      previous := (737)
      next := (0)
      square := (18817589225178321790665769794000000000000)
      linear := (72242738729586996215825679120000000000000)
      constant := (7278942732038472700199562835860000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree001.table
  base := (150381698679473624626578471647409778290401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (4760676248835151080363026273640000000000000)
      constant := (388791535531009907392048442029672833333333001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree001.table
  base := (18633452480789844585767084623597790913751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (42657910347264576505360578764820000000000000)
      constant := (3468083123548319866387011040386815499999977272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49526788001235641567/100000000000000000000)
  directionHi := (1547712125038613799/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree002.table
  base := (97838375635517501561413428390018892306377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (3380719705655407482380869822080000000000000)
      constant := (250370364930946773570334892810279138888886577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree002.table
  base := (12034637012266456557226337458965692949293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (30050125566395100905614513002840000000000000)
      constant := (2216390019773363504334444148651463249999998696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/100000000000000000000)
  centralHi := (1547712125038613799/3125000000000000000)
  directionLo := (2188795477878891139/3125000000000000000)
  directionHi := (70041455292124516449/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree003.table
  base := (65699733165434218375984239834339493190763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (666921054158554628132904456840000000000000)
      constant := (55205681291698209602759064229452340596391521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree003.table
  base := (64285486548833741686533259442011361929031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (1938037865058402811763160804540000000000000)
      constant := (161899972728968415736111644901881552377409631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2188795477878891139/3125000000000000000)
  centralHi := (70041455292124516449/100000000000000000000)
  directionLo := (5361432072114548443/6250000000000000000)
  directionHi := (85782913153832775089/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree004.table
  base := (45548996173146223196264952755908186025343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (620806619295920286416556918960000000000000)
      constant := (112639540338555760681533837327077191851917143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree004.table
  base := (8877144092521164022624255528089686510901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (966911200931229941224476295776000000000000)
      constant := (197277701811116965151095263690043471533681509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5361432072114548443/6250000000000000000)
  centralHi := (85782913153832775089/100000000000000000000)
  directionLo := (49526788001235641567/50000000000000000000)
  directionHi := (19810715200494256627/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree005.table
  base := (6501516334336467248935931931810930017703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-151829984776764662313119906520000000000000)
      constant := (15749731994443626117725978266040228976045503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree005.table
  base := (987073778576101205068791281782170727853/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-7773228776213325893623684283100000000000000)
      constant := (687411736280349652179541992701892706185948064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/50000000000000000000)
  centralHi := (19810715200494256627/20000000000000000000)
  directionLo := (55372632338991916439/50000000000000000000)
  directionHi := (110745264677983832879/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree006.table
  base := (23749163901752334679293729062203846257883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-713035489021188969849251994720000000000000)
      constant := (18864376492055956305897792738050734705584561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree006.table
  base := (11513210126713060647407739341423907020739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-2264557061898089054818861116120000000000000)
      constant := (54799619590576518413770676763727164321884278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55372632338991916439/50000000000000000000)
  centralHi := (110745264677983832879/100000000000000000000)
  directionLo := (6065767960101184149/5000000000000000000)
  directionHi := (121315359202023682981/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree007.table
  base := (17620624865420963988625085145931161405313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-3519063010243310507529912435720000000000000)
      constant := (41873188937775378684359418772606950815219113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree007.table
  base := (17049703322435111324296270957041814980371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-32988798337952277093115815807060000000000000)
      constant := (364973156726533022687759581115881846875504739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/5000000000000000000)
  centralHi := (121315359202023682981/100000000000000000000)
  directionLo := (65517782143543616389/50000000000000000000)
  directionHi := (131035564287087232779/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree008.table
  base := (6573514674361596754122337649397366610303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-4899019553423054105512068887280000000000000)
      constant := (32053031865517615130448047163205101106796206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree008.table
  base := (12688870201221829736430656020355199616063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-45596583118821752692861881569040000000000000)
      constant := (280097017321475693068199367481934867812418767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65517782143543616389/50000000000000000000)
  centralHi := (131035564287087232779/100000000000000000000)
  directionLo := (2188795477878891139/1562500000000000000)
  directionHi := (140082910584249032897/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree009.table
  base := (2436680066649475517357991667003978244249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-2092992032200932567831408446280000000000000)
      constant := (8539922727050200698705719145289796551055532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree009.table
  base := (374872616820770589332145429148415460663/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-1293430397770916184280176607356000000000000)
      constant := (5003905359332115504174739075933143065922315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2188795477878891139/1562500000000000000)
  centralHi := (140082910584249032897/100000000000000000000)
  directionLo := (148580364003706924701/100000000000000000000)
  directionHi := (74290182001853462351/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree010.table
  base := (1766809105629989927799252909226710212021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-7658932639782541301476381790400000000000000)
      constant := (21656646312512476552831895839594693045866484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree010.table
  base := (6754429930072911010203865045658289555831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-70812152680560703892354013093000000000000000)
      constant := (192154079514533821868763377962814900212447879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148580364003706924701/100000000000000000000)
  centralHi := (74290182001853462351/50000000000000000000)
  directionLo := (156617455276202809203/100000000000000000000)
  directionHi := (39154363819050702301/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree011.table
  base := (1222659383243421220100850609746752342687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-9038889182962284899458538241960000000000000)
      constant := (19596803582178950780884465773765211373315548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree011.table
  base := (925030033703713835516355885446931068607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-16683987492286035898420015770996000000000000)
      constant := (35215908189453404420186793941949209385021263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156617455276202809203/100000000000000000000)
  centralHi := (39154363819050702301/25000000000000000000)
  directionLo := (32852354574314898487/20000000000000000000)
  directionHi := (41065443217893623109/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree012.table
  base := (769679581562032458066485620189899086603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-3472948575380676165813564897840000000000000)
      constant := (6360256026143283232029523632898570032339204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree012.table
  base := (1425152631346623213132143187530490991511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-10669746915811072787982904957440000000000000)
      constant := (19313669333141366634938012373693614137840222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32852354574314898487/20000000000000000000)
  centralHi := (41065443217893623109/25000000000000000000)
  directionLo := (171565826307665550177/100000000000000000000)
  directionHi := (85782913153832775089/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree013.table
  base := (308234329330926260941673435713593920877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-2359760453864354419084570229016000000000000)
      constant := (3974730177863792030756769406459057788201077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree013.table
  base := (671339130778059157116983107319923593143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-108635507023169130691592210378940000000000000)
      constant := (183342867060634995346102025762994182783768974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171565826307665550177/100000000000000000000)
  centralHi := (85782913153832775089/50000000000000000000)
  directionLo := (89285686823744884191/50000000000000000000)
  directionHi := (178571373647489768383/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree014.table
  base := (216976647108298188733174493890886115877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-13178758812501515693405007596640000000000000)
      constant := (21816736791578480379467791372370194787396077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree014.table
  base := (43300672216597493603823213013746740881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-121243291804038606291338276140920000000000000)
      constant := (203258676684279349769227029796198797457283329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89285686823744884191/50000000000000000000)
  centralHi := (178571373647489768383/100000000000000000000)
  directionLo := (7412490886720413853/4000000000000000000)
  directionHi := (92656136084005173163/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree015.table
  base := (-936572907624810670067182606155846836537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-4852905118560419763795721349400000000000000)
      constant := (8266315622454976476842124695462880792722421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree015.table
  base := (-217837711308180578995804476974719166961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-2974468368553512930912985375620000000000000)
      constant := (5168938489362215337627234695038755446734439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7412490886720413853/4000000000000000000)
  centralHi := (92656136084005173163/50000000000000000000)
  directionLo := (191816425119930959311/100000000000000000000)
  directionHi := (11988526569995684957/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree016.table
  base := (-121900688731494672481742721878745523063/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-15938671898861002889369320499760000000000000)
      constant := (28739821777062177418632113480854126312210192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree016.table
  base := (-2084842836793438923051863209238815901883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-146458861365777557490830407664880000000000000)
      constant := (270670012748384211039481137023888558552820853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191816425119930959311/100000000000000000000)
  centralHi := (11988526569995684957/6250000000000000000)
  directionLo := (49526788001235641567/25000000000000000000)
  directionHi := (198107152004942566269/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree017.table
  base := (-711915251695996040315081440793620832167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4785)
      previous := (3630)
      next := (0)
      square := (94087946125891608953328848970000000000000)
      linear := (-1018742849531808616903028055960000000000000)
      constant := (1975248104202920421348135579554304050713796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree017.table
  base := (-2966202144859783575129098820679092456697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42570)
      previous := (33165)
      next := (0)
      square := (846791515133024480579959640730000000000000)
      linear := (-9356861538038060770033910201580000000000000)
      constant := (18643198856463926794911539866094889687128231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/25000000000000000000)
  centralHi := (198107152004942566269/100000000000000000000)
  directionLo := (204204178226667923803/100000000000000000000)
  directionHi := (51051044556666980951/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree018.table
  base := (-3646082608457744257125395219858242917629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-6232861661740163361777877800960000000000000)
      constant := (13090313922615553314586747927262903390415657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree018.table
  base := (-3750629445409646169491637171916114279941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-19074936769724056521146948798760000000000000)
      constant := (41220987312872677575959212123406186757873459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204204178226667923803/100000000000000000000)
  centralHi := (51051044556666980951/25000000000000000000)
  directionLo := (6566386433636673417/3125000000000000000)
  directionHi := (42024873175274709869/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree019.table
  base := (-4359621674853618847456590350251071286809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-20078541528400233683315789854440000000000000)
      constant := (45778720610069185456958680852156963583009791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree019.table
  base := (-890357897882106608526650480863431778433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-36856443141677196858013720990164000000000000)
      constant := (86502730072177576643781714461949925498661903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6566386433636673417/3125000000000000000)
  centralHi := (42024873175274709869/20000000000000000000)
  directionLo := (1349264149347180907/625000000000000000)
  directionHi := (215882263895548945121/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree020.table
  base := (-4999420968968653842153242755539442748451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-21458498071579977281297946306000000000000000)
      constant := (53073571971561907290865454568841909411278949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree020.table
  base := (-5080615404909856296740357498921407874781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-196890000489255459889814670712800000000000000)
      constant := (501252740600526240719241425847748763059251571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1349264149347180907/625000000000000000)
  centralHi := (215882263895548945121/100000000000000000000)
  directionLo := (221490529355967665757/100000000000000000000)
  directionHi := (110745264677983832879/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree021.table
  base := (-1114900332410384272692866027361869924773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-1522563640983981391952006850504000000000000)
      constant := (4075468785727065923700731595421258775221809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree021.table
  base := (-2822981630335200102770516293241789862553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-23277531696680548387728970719420000000000000)
      constant := (64110982757900128180103426882646209134999294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221490529355967665757/100000000000000000000)
  centralHi := (110745264677983832879/50000000000000000000)
  directionLo := (226960254943692978381/100000000000000000000)
  directionHi := (113480127471846489191/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree022.table
  base := (-304611952815763168384410503489127947723/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-4843682231587892895452451841824000000000000)
      constant := (13986983378409685844512642177027112831889908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree022.table
  base := (-6155071734092851394868107679899279679069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-222105570050994411089306802236760000000000000)
      constant := (659582512823339948699856102826077761992673779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226960254943692978381/100000000000000000000)
  centralHi := (113480127471846489191/50000000000000000000)
  directionLo := (232301226974429585661/100000000000000000000)
  directionHi := (116150613487214792831/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree023.table
  base := (-3279353093267765858935846836586959685279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-25598367701119208075244415660680000000000000)
      constant := (79466431326534636696237409710514635717178642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree023.table
  base := (-6613896329640419355574473268449959428909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-234713354831863886689052867998740000000000000)
      constant := (748864332203263354984641895030944899728669219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232301226974429585661/100000000000000000000)
  centralHi := (116150613487214792831/50000000000000000000)
  directionLo := (237522131144752047219/100000000000000000000)
  directionHi := (11876106557237602361/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree024.table
  base := (-1395785977473652313423317945682569648637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-1798554949619930111548438140816000000000000)
      constant := (5980900019495037622887717717797212114631721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree024.table
  base := (-7027360051499662885179596472192451021201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-27480126623637040254310992640080000000000000)
      constant := (93858784483985357509350556971667434893856199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237522131144752047219/100000000000000000000)
  centralHi := (11876106557237602361/5000000000000000000)
  directionLo := (6065767960101184149/2500000000000000000)
  directionHi := (242630718404047365961/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree025.table
  base := (-11495448215566880582114225688244846763/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-5671656157495739054241745712760000000000000)
      constant := (20133052039046750220920522543064019656887936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree025.table
  base := (-7399546393141295812728924651911616581113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-259928924393602837888544999522700000000000000)
      constant := (947081106782498596474270578699650967452725783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/2500000000000000000)
  centralHi := (242630718404047365961/100000000000000000000)
  directionLo := (49526788001235641567/20000000000000000000)
  directionHi := (61908485001544551959/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree026.table
  base := (-7696657149067416044894355520360570450333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-29738237330658438869190885015360000000000000)
      constant := (112312659422962977113933131389302156258683867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree026.table
  base := (-7733851055962950992643460146723723628071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-272536709174472313488291065284680000000000000)
      constant := (1055840981509137304165847349138504353590485961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/20000000000000000000)
  centralHi := (61908485001544551959/25000000000000000000)
  directionLo := (63134514615968383267/25000000000000000000)
  directionHi := (252538058463873533069/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree027.table
  base := (-8000546429236924607208030461824216301879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-10372731291279394155724347155640000000000000)
      constant := (41549380110567380308569422205878404466270907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree027.table
  base := (-8033103154491104428982806929479367458409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-31682721550593532120893014560740000000000000)
      constant := (130104717532648229319983783851234165240678191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63134514615968383267/25000000000000000000)
  centralHi := (252538058463873533069/100000000000000000000)
  directionLo := (128674369730749162633/50000000000000000000)
  directionHi := (257348739461498325267/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree028.table
  base := (-8271184678614170483369201802518210990787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-32498150417017926065155197918480000000000000)
      constant := (137665382543099712516628954729890133212963013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree028.table
  base := (-8299663212793147900610586026647901231449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-297752278736211264687783196808640000000000000)
      constant := (1292330278128695301464872190658839280073010359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128674369730749162633/50000000000000000000)
  centralHi := (257348739461498325267/100000000000000000000)
  directionLo := (262071128574174465557/100000000000000000000)
  directionHi := (131035564287087232779/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree029.table
  base := (-8510606642063251341089820416832675469737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-33878106960197669663137354370040000000000000)
      constant := (151359093685764173852976411501778211103214063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree029.table
  base := (-4267751547016699195870855639109504804417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-310360063517080740287529262570620000000000000)
      constant := (1419958283168907520637414839051381204066804894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262071128574174465557/100000000000000000000)
  centralHi := (131035564287087232779/50000000000000000000)
  directionLo := (133354957877332801061/50000000000000000000)
  directionHi := (266709915754665602123/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree030.table
  base := (-545032367900911738218415584146135815543/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-11752687834459137753706503607200000000000000)
      constant := (55241612526789866957731709420724803966787504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree030.table
  base := (-1092783951082254927705833249531955039411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-35885316477550023987475036481400000000000000)
      constant := (172643097323415112377208806220739079539935912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133354957877332801061/50000000000000000000)
  centralHi := (266709915754665602123/100000000000000000000)
  directionLo := (67817347472632399413/25000000000000000000)
  directionHi := (271269389890529597653/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree031.table
  base := (-2225587330472020674841933171524432917973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-36638020046557156859101667273160000000000000)
      constant := (180758892429434026382041806319819799921408908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree031.table
  base := (-4460674306841777999820502819205620010883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-335575633078819691487021394094580000000000000)
      constant := (1693786755281281876154197603756441282330479706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67817347472632399413/25000000000000000000)
  centralHi := (271269389890529597653/100000000000000000000)
  directionLo := (137876742619358668427/50000000000000000000)
  directionHi := (55150697047743467371/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree032.table
  base := (-4528651186637843462259915263255088659137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-38017976589736900457083823724720000000000000)
      constant := (196458133327073586037088658679587028795169326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree032.table
  base := (-4536944884700749028957010373493919524837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-348183417859689167086767459856560000000000000)
      constant := (1839927868428780222552750780056001675686181334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137876742619358668427/50000000000000000000)
  centralHi := (55150697047743467371/20000000000000000000)
  directionLo := (280165821168498065793/100000000000000000000)
  directionHi := (140082910584249032897/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree033.table
  base := (-9186386508325742114013177190382946792761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-13132644377638881351688660058760000000000000)
      constant := (70939978215891614422115604622617985130676213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree033.table
  base := (-2300215914071796519044154927598460686387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-40087911404506515854057058402060000000000000)
      constant := (221354282428098252608998458935675615018829652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280165821168498065793/100000000000000000000)
  centralHi := (140082910584249032897/50000000000000000000)
  directionLo := (56901947270981219953/20000000000000000000)
  directionHi := (142254868177453049883/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree034.table
  base := (-2322612620147768864365748234139110803373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4785)
      previous := (3630)
      next := (0)
      square := (94087946125891608953328848970000000000000)
      linear := (-2398699392711552214885184507520000000000000)
      constant := (13520122869602758502919240234786864188335724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree034.table
  base := (-9303082611516757151085337725076342147303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42570)
      previous := (33165)
      next := (0)
      square := (846791515133024480579959640730000000000000)
      linear := (-21964646318907536369779975963560000000000000)
      constant := (126502927032508107979015930731649876863163769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56901947270981219953/20000000000000000000)
  centralHi := (142254868177453049883/50000000000000000000)
  directionLo := (144394159170703227877/50000000000000000000)
  directionHi := (57757663668281291151/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree035.table
  base := (-9370208379981601329466874627377869243359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-42157846219276131251030293079400000000000000)
      constant := (247522738385934052598601119611190162098023241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree035.table
  base := (-1172653547873528674286148621224775832087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-386006772202297593886005657142500000000000000)
      constant := (2314995562491496203064013083196243780373403336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144394159170703227877/50000000000000000000)
  centralHi := (57757663668281291151/20000000000000000000)
  directionLo := (58600885843194164143/20000000000000000000)
  directionHi := (73251107303992705179/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree036.table
  base := (-9426261380277638668654305633149201456921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-14512600920818624949670816510320000000000000)
      constant := (88620106600911235951297878160379642336849493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree036.table
  base := (-2358968373764381142289215899915748947799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-44290506331463007720639080322720000000000000)
      constant := (276168060938534622576057249428316547947099204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58600885843194164143/20000000000000000000)
  centralHi := (73251107303992705179/25000000000000000000)
  directionLo := (148580364003706924701/50000000000000000000)
  directionHi := (297160728007413849403/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree037.table
  base := (-2364778978035065965037174358652885046059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-44917759305635618446994605982520000000000000)
      constant := (284853515807496400637798635339815383980802164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree037.table
  base := (-9467499058751077990851802362970306387949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-411222341764036545085497788666460000000000000)
      constant := (2662089455090566211712116322936918097764501859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148580364003706924701/50000000000000000000)
  centralHi := (297160728007413849403/100000000000000000000)
  directionLo := (301259690299939617539/100000000000000000000)
  directionHi := (15062984514996980877/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree038.table
  base := (-1893839772318241495283372382496573062199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-9259543169763072408995352486816000000000000)
      constant := (60900243213935921946265988897094413465220401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree038.table
  base := (-9476509629545883792068427265460884943961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-423830126544906020685243854428440000000000000)
      constant := (2844716812183599072994572592710066144346816951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301259690299939617539/100000000000000000000)
  centralHi := (15062984514996980877/5000000000000000000)
  directionLo := (305303625476892873407/100000000000000000000)
  directionHi := (4770369148076451147/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree039.table
  base := (-1891374057983515507350788311060085071451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-3178511492799673709530594592376000000000000)
      constant := (21653498937991704478420059753694906243051983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree039.table
  base := (-9463245610645590257314707847566686505491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-48493101258419499587221102243380000000000000)
      constant := (337042961247479553815537443911369048399217909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305303625476892873407/100000000000000000000)
  centralHi := (4770369148076451147/1562500000000000000)
  directionLo := (309294691934818386593/100000000000000000000)
  directionHi := (154647345967409193297/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree040.table
  base := (-1884486817218490054810121280990635723497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-9811525787034969848188215067440000000000000)
      constant := (69151305878573060338192571604143356483184303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree040.table
  base := (-9427993613794623427064641828216059499947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-449045696106644971884735985952400000000000000)
      constant := (3228092262927391676566453717811290263165740677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309294691934818386593/100000000000000000000)
  centralHi := (154647345967409193297/50000000000000000000)
  directionLo := (156617455276202809203/50000000000000000000)
  directionHi := (313234910552405618407/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree041.table
  base := (-9366146893142353057903640069499109082809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-50437585478354592838923231788760000000000000)
      constant := (367362684510136815586994595466792817275613791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree041.table
  base := (-2342748779793507980606958881183235615047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-461653480887514447484482051714380000000000000)
      constant := (3428827994474267982502867986254736549949459108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156617455276202809203/50000000000000000000)
  centralHi := (313234910552405618407/100000000000000000000)
  directionLo := (158563088326455163799/50000000000000000000)
  directionHi := (317126176652910327599/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree042.table
  base := (-9288225592461416522299283760052785031733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-17272514007178112145635129413440000000000000)
      constant := (129873461771061325028465965084514235377487489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree042.table
  base := (-1858490743569316258151791634971257822157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-10539139237075198290760624832808000000000000)
      constant := (80790868444550147187801207741031758404569643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158563088326455163799/50000000000000000000)
  centralHi := (317126176652910327599/100000000000000000000)
  directionLo := (64194054132205180757/20000000000000000000)
  directionHi := (160485135330512951893/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree043.table
  base := (-287151674455389151635657662690451624019/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-53197498564714080034887544691880000000000000)
      constant := (412529154782448945692718533776588330429650592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree043.table
  base := (-4596270586125710123651241131500309740999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-486869050449253398683974183238340000000000000)
      constant := (3848371498731919567135854947698708498545908818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64194054132205180757/20000000000000000000)
  centralHi := (160485135330512951893/50000000000000000000)
  directionLo := (162384433812120338949/50000000000000000000)
  directionHi := (324768867624240677899/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree044.table
  base := (-9068186049459325878130919371200158382849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-54577455107893823632869701143440000000000000)
      constant := (436088589279187697586861222135668388046209751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree044.table
  base := (-9071402490555868755079380620380960742763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-499476835230122874283720249000320000000000000)
      constant := (4067171856159568020542911831305662089972660933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162384433812120338949/50000000000000000000)
  centralHi := (324768867624240677899/100000000000000000000)
  directionLo := (328523545743148984871/100000000000000000000)
  directionHi := (41065443217893623109/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree045.table
  base := (-4463177196448986586007219473357619327941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-18652470550357855743617285865000000000000000)
      constant := (153432782344194339047385076600197888085350306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree045.table
  base := (-558072511111256370259997298051561126191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-56898291112332483320385146084700000000000000)
      constant := (476887476063076078280065473780536232172435344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328523545743148984871/100000000000000000000)
  centralHi := (41065443217893623109/12500000000000000000)
  directionLo := (66447158806790299727/20000000000000000000)
  directionHi := (83058948508487874659/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree046.table
  base := (-8763469946027847774391282686187580765411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-57337368194253310828834014046560000000000000)
      constant := (485158138465139187000520992333386102429165989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree046.table
  base := (-4382958899662643249382565032324788919239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-524692404791861825483212380524280000000000000)
      constant := (4522815359593793706753419744644178032379068498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66447158806790299727/20000000000000000000)
  centralHi := (83058948508487874659/25000000000000000000)
  directionLo := (67181403845733852283/20000000000000000000)
  directionHi := (41988377403583657677/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree047.table
  base := (-8579627102780115627314700943023822910143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-58717324737433054426816170498120000000000000)
      constant := (510667718058241244546678005564835036610718057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree047.table
  base := (-8581762969882305503015433205232806538671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-537300189572731301082958446286260000000000000)
      constant := (4759654030265596146529765723250795231736250561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67181403845733852283/20000000000000000000)
  centralHi := (41988377403583657677/12500000000000000000)
  directionLo := (84884638000939589787/25000000000000000000)
  directionHi := (339538552003758359149/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree048.table
  base := (-8374905948933935339108581824385912757619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-20032427093537599341599442316560000000000000)
      constant := (178942292502925866080125278842737413639144327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree048.table
  base := (-4188384930938639976447504533675492705559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-61100886039288975186967168005360000000000000)
      constant := (555833506697863217442939377693580086945682082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84884638000939589787/25000000000000000000)
  centralHi := (339538552003758359149/100000000000000000000)
  directionLo := (171565826307665550177/50000000000000000000)
  directionHi := (68626330523066220071/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree049.table
  base := (-4074687238432821751556041500345049603601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-61477237823792541622780483401240000000000000)
      constant := (563635439968577396602339336122765051962067598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree049.table
  base := (-8151001311964002194336406251383634781291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-562515759134470252282450577810220000000000000)
      constant := (5251356478696083513097550742432170493404758981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171565826307665550177/50000000000000000000)
  centralHi := (68626330523066220071/20000000000000000000)
  directionLo := (346687516008649490969/100000000000000000000)
  directionHi := (34668751600864949097/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree050.table
  base := (-1975772612739393702530360437558924955361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-62857194366972285220762639852800000000000000)
      constant := (591093255192482187101807491187636944764424156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree050.table
  base := (-7904510591059690203649353215380574957327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-575123543915339727882196643572200000000000000)
      constant := (5506217538492638659255620319346156120823932257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346687516008649490969/100000000000000000000)
  centralHi := (34668751600864949097/10000000000000000000)
  directionLo := (350207276460622582241/100000000000000000000)
  directionHi := (175103638230311291121/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree051.table
  base := (-76361029797048243753111193511163440351/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102000000000000000000000000000000000000000
      center := (319)
      previous := (242)
      next := (0)
      square := (6272529741726107263555256598000000000000)
      linear := (-251910395726086387524489397272000000000000)
      constant := (2428236060585475401349849129170613290841980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree051.table
  base := (-1909335723147739391204995727323288740381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4730)
      previous := (3685)
      next := (0)
      square := (94087946125891608953328848970000000000000)
      linear := (-3841381233308556885502893525060000000000000)
      constant := (37693357396977194758647919893848147290886828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350207276460622582241/100000000000000000000)
  centralHi := (175103638230311291121/50000000000000000000)
  directionLo := (353692011806439126581/100000000000000000000)
  directionHi := (176846005903219563291/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree052.table
  base := (-7348453841435793593860613271766280289433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-65617107453331772416726952755920000000000000)
      constant := (647956152073587345300689573459975904967184767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree052.table
  base := (-183738414615019069044148885592745117309/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-120067822695415735816337755019232000000000000)
      constant := (1206790802054636462880011302121883436391308952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353692011806439126581/100000000000000000000)
  centralHi := (176846005903219563291/50000000000000000000)
  directionLo := (71428549458995907353/20000000000000000000)
  directionHi := (178571373647489768383/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree053.table
  base := (-3520089301471980864718929959693252909181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-66997063996511516014709109207480000000000000)
      constant := (677361032556125701406441325156915698366440438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree053.table
  base := (-3520562131928638295222479318721879593967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-612946898257948154681434840858140000000000000)
      constant := (6306827761041907098073821104342969041169652994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71428549458995907353/20000000000000000000)
  centralHi := (178571373647489768383/50000000000000000000)
  directionLo := (72112091822419061467/20000000000000000000)
  directionHi := (45070057389011913417/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree054.table
  base := (-1677826890990798012638585771688588743543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-22792340179897086537563755219680000000000000)
      constant := (235804919362434505766689471228103974237392876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree054.table
  base := (-3356066821923797661313741435562839765733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-69506075893201958920131211846680000000000000)
      constant := (731744920588740634718727790782642107538656934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72112091822419061467/20000000000000000000)
  centralHi := (45070057389011913417/12500000000000000000)
  directionLo := (18197303880303552447/5000000000000000000)
  directionHi := (363946077606071048941/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree055.table
  base := (-1272373311019700912956972711453203513251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-13951395416574200642134684422120000000000000)
      constant := (147623452296343427188373756440910217662034149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree055.table
  base := (-636258830332198872955667181954636852073/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-127632493563937421176185394476420000000000000)
      constant := (1374116606217698618501842559592097811859646286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18197303880303552447/5000000000000000000)
  centralHi := (363946077606071048941/100000000000000000000)
  directionLo := (3673004902454713977/1000000000000000000)
  directionHi := (367300490245471397701/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree056.table
  base := (-5991877612375177311303726445928937246573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-71136933626050746808655578562160000000000000)
      constant := (769468485423664809151950063113498834221663627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree056.table
  base := (-599250831770280826437140167230152898747/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-130154050520111316296134607628816000000000000)
      constant := (1432292705693165482605856238874170701586462954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3673004902454713977/1000000000000000000)
  centralHi := (367300490245471397701/100000000000000000000)
  directionLo := (7412490886720413853/2000000000000000000)
  directionHi := (370624544336020692651/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree057.table
  base := (-5601359547846917617006534075621373209669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-24172296723076830135545911671240000000000000)
      constant := (267156126994331614724352264923116269427216977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree057.table
  base := (-5601910792040949791172235096404661410483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-73708670820158450786713233767340000000000000)
      constant := (828705041890948028082891692755861475671333717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7412490886720413853/2000000000000000000)
  centralHi := (370624544336020692651/100000000000000000000)
  directionLo := (373919049520083032109/100000000000000000000)
  directionHi := (37391904952008303211/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree058.table
  base := (-5190328432588477177532353330008742927739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-73896846712410234004619891465280000000000000)
      constant := (834116906358841811844831764207687259644950861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree058.table
  base := (-81106411112049612160481422096340153403/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-675985822162295532680165169668040000000000000)
      constant := (7761228235330210671084137763723833494335307072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373919049520083032109/100000000000000000000)
  centralHi := (37391904952008303211/10000000000000000000)
  directionLo := (37718478007963370833/10000000000000000000)
  directionHi := (377184780079633708331/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree059.table
  base := (-594849750723668836313383047734077018071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-75276803255589977602602047916840000000000000)
      constant := (867414025815573836458750057099109325407978632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree059.table
  base := (-19036877280741544127987195970454838069/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-137718721388633001655982247086004000000000000)
      constant := (1614022362414741268668209509247903134782138950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37718478007963370833/10000000000000000000)
  centralHi := (377184780079633708331/100000000000000000000)
  directionLo := (76084495412256230389/20000000000000000000)
  directionHi := (190211238530640575973/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree060.table
  base := (-4306780021479669304600294478473468528713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-25552253266256573733528068122800000000000000)
      constant := (300453236260319515632373990991163502785605829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree060.table
  base := (-4307148446226789507380106630880685883619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-77911265747114942653295255688000000000000000)
      constant := (931666206497580437024962163929079336016706981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76084495412256230389/20000000000000000000)
  centralHi := (190211238530640575973/50000000000000000000)
  directionLo := (191816425119930959311/50000000000000000000)
  directionHi := (383632850239861918623/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree061.table
  base := (-3834284542587533119026895402433596841733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-78036716341949464798566360819960000000000000)
      constant := (935953929081319954801889682344230214614652467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree061.table
  base := (-1917303385419265741901767684037537627931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-713809176504903959479403366953980000000000000)
      constant := (8705880161953919938844501552202340563335526442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191816425119930959311/50000000000000000000)
  centralHi := (383632850239861918623/100000000000000000000)
  directionLo := (96704144983837062279/25000000000000000000)
  directionHi := (386816579935348249117/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree062.table
  base := (-417665023811353650055111900782814176261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-79416672885129208396548517271520000000000000)
      constant := (971196664292454175912686058246751202620361112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree062.table
  base := (-5221253219719044058653214175870285581/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-145283392257154687015829886543192000000000000)
      constant := (1806552908138492976017141319258990718058799488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96704144983837062279/25000000000000000000)
  centralHi := (386816579935348249117/100000000000000000000)
  directionLo := (24373394918515195331/6250000000000000000)
  directionHi := (389974318696243125297/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree063.table
  base := (-353486794617209554446405754061977017589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-26932209809436317331510224574360000000000000)
      constant := (335695965062808117668376365386106127406002696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree063.table
  base := (-2828140962706575011910947512501526666349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-82113860674071434519877277608660000000000000)
      constant := (1040627648787897762678682934353593529140826251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24373394918515195331/6250000000000000000)
  centralHi := (389974318696243125297/100000000000000000000)
  directionLo := (12284584151914428073/3125000000000000000)
  directionHi := (393106692861261698337/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree064.table
  base := (-573503346031913922491591656956445365657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-82176585971488695592512830174640000000000000)
      constant := (1043627605273169376247927358918785142415704572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree064.table
  base := (-35847330789777490775146673939128948129/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-751632530847512386278641564239920000000000000)
      constant := (9704532923871839079209596783846331549007887296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12284584151914428073/3125000000000000000)
  centralHi := (393106692861261698337/100000000000000000000)
  directionLo := (49526788001235641567/12500000000000000000)
  directionHi := (396214304009885132537/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree065.table
  base := (-869841358918610746078896409415521050739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-83556542514668439190494986626200000000000000)
      constant := (1080815780382224687412370321843220459494055722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree065.table
  base := (-1739871564583740103236393686156953925603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-764240315628381861878387630001900000000000000)
      constant := (10049416680788382141526733677665001865555559373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/12500000000000000000)
  centralHi := (396214304009885132537/100000000000000000000)
  directionLo := (199648865155650845069/50000000000000000000)
  directionHi := (399297730311301690139/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree066.table
  base := (-1164907037709004330778271308531521835743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-28312166352616060929492381025920000000000000)
      constant := (372884136114613268199174736919023170568410819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree066.table
  base := (-1165072331734308781545723253409132526341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-86316455601027926386459299529320000000000000)
      constant := (1155588890203249344601946712732322846298987059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199648865155650845069/50000000000000000000)
  centralHi := (399297730311301690139/100000000000000000000)
  directionLo := (201178763890150912747/50000000000000000000)
  directionHi := (80471505556060365099/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree067.table
  base := (-28484518409129303971729369229351655189/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-17263291120205585277291859905864000000000000)
      constant := (231427495738089475070027555425425825379413644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree067.table
  base := (-113967013380218063443776242364100358657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-157891177038024162615575952305172000000000000)
      constant := (2151436566568265200847471127046276774704198287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201178763890150912747/50000000000000000000)
  centralHi := (80471505556060365099/20000000000000000000)
  directionLo := (101348557861963338707/25000000000000000000)
  directionHi := (405394231447853354829/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree068.table
  base := (574547837448606424546959943663781959/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (957)
      previous := (726)
      next := (0)
      square := (18817589225178321790665769794000000000000)
      linear := (-1031722495814207882169899482128000000000000)
      constant := (14073776263680513849187040068726088938235632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree068.table
  base := (2291857034727966905628589464016554331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2754000000000000000000000000000000000000000
      center := (8514)
      previous := (6633)
      next := (0)
      square := (169358303026604896115991928146000000000000)
      linear := (-9436043176129297513854421497504000000000000)
      constant := (130824294958929942688405836898191803181255148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101348557861963338707/25000000000000000000)
  centralHi := (405394231447853354829/100000000000000000000)
  directionLo := (408408356453335847607/100000000000000000000)
  directionHi := (51051044556666980951/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree069.table
  base := (68205256420264730477772177942552478143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-5938424579159160905494907495496000000000000)
      constant := (82403527450041551916106663685696385997099962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree069.table
  base := (340970817028630906194507883499498582193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-90519050527984418253041321449980000000000000)
      constant := (1276549629514977406881933141528454391624567986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408408356453335847607/100000000000000000000)
  centralHi := (51051044556666980951/12500000000000000000)
  directionLo := (411400399064748564319/100000000000000000000)
  directionHi := (2571252494154678527/625000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree070.table
  base := (53542930848167012266161401836043561423/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-18091265046113431436081153776800000000000000)
      constant := (255296652002681361510547512726077746516306115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree070.table
  base := (167309515734092857251324524542377633469/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-827279239532729239877117958811800000000000000)
      constant := (11863827561674840758643997052885100144175006568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411400399064748564319/100000000000000000000)
  centralHi := (2571252494154678527/625000000000000000)
  directionLo := (41437083763261346347/10000000000000000000)
  directionHi := (414370837632613463471/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree071.table
  base := (2015523728487246996868628892196201051533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-91836281773746900778387925335560000000000000)
      constant := (1317562021428240364029705930781762318935037333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree071.table
  base := (2015438645218906098099902694427986074031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-839887024313598715476864024573780000000000000)
      constant := (12244707713491862064547969174080674726006991679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41437083763261346347/10000000000000000000)
  centralHi := (414370837632613463471/100000000000000000000)
  directionLo := (417320133482765301421/100000000000000000000)
  directionHi := (208660066741382650711/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree072.table
  base := (1356451009573255625870024045458424211271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-31072079438975548125456693929040000000000000)
      constant := (453096397003084376633269863897704907582343914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree072.table
  base := (54256549842675987891403209450911527597/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-18944329090988182023924668674128000000000000)
      constant := (280701935139810027601085362806970208832797970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417320133482765301421/100000000000000000000)
  centralHi := (208660066741382650711/50000000000000000000)
  directionLo := (420248731752747098689/100000000000000000000)
  directionHi := (42024873175274709869/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree073.table
  base := (686141297210943607041106323849203978007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-18919238972021277594870447647736000000000000)
      constant := (280332952889251425563849860988819779546796207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree073.table
  base := (1715320599428663871239811583058672098707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-865102593875337666676356156097740000000000000)
      constant := (13024465630714812227175932168935730910317264326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420248731752747098689/100000000000000000000)
  centralHi := (42024873175274709869/10000000000000000000)
  directionLo := (423157062176104685011/100000000000000000000)
  directionHi := (105789265544026171253/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree074.table
  base := (13027924047608124924915458992108563127/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-19195230280657226314466878938048000000000000)
      constant := (288937747601895497071058846728574359852372928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree074.table
  base := (1042219624186371002240180873473031857693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-877710378656207142276102221859720000000000000)
      constant := (13423343332064257456955944819460080811026941748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423157062176104685011/100000000000000000000)
  centralHi := (105789265544026171253/25000000000000000000)
  directionLo := (2662784623865580961/625000000000000000)
  directionHi := (426045539818492953761/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree075.table
  base := (2463794202257627607446113408289874602547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-32452035982155291723438850380600000000000000)
      constant := (496120369489342562257431684464974642560816498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree075.table
  base := (1231884572002311581445468114325891941517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-98924240381897401986205365291300000000000000)
      constant := (1536468906626849302052827334557696579759542868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2662784623865580961/625000000000000000)
  centralHi := (426045539818492953761/100000000000000000000)
  directionLo := (428914565769163875443/100000000000000000000)
  directionHi := (107228641442290968861/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree076.table
  base := (114133270733887528266884329619322774359/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-19747212897929123753659741518672000000000000)
      constant := (306536374604020906136500668432150585361077590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree076.table
  base := (1141323924311938176159629522603964346971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-180585189643589218695118870676736000000000000)
      constant := (2847819218236586078843187050827468201398244139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428914565769163875443/100000000000000000000)
  centralHi := (107228641442290968861/25000000000000000000)
  directionLo := (1349264149347180907/312500000000000000)
  directionHi := (431764527791097890241/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree077.table
  base := (6506160156544826400913331473662598006301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-100116021032825362366280864044920000000000000)
      constant := (1577651029233182233305668164923836417414388901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree077.table
  base := (3253060836175055912861068295249546184977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-915533732998815569075340419145660000000000000)
      constant := (14655971107374599146974852512632283253288253186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1349264149347180907/312500000000000000)
  centralHi := (431764527791097890241/100000000000000000000)
  directionLo := (217297900466381106451/50000000000000000000)
  directionHi := (434595800932762212903/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree078.table
  base := (457879840693951610513492996803201788993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-33831992525335035321421006832160000000000000)
      constant := (541089524997581014932660853333734015216910896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree078.table
  base := (7326043723698227230782305829158700875357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-103126835308853893852787387211960000000000000)
      constant := (1675427243493314937673130661931601780976803557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217297900466381106451/50000000000000000000)
  centralHi := (434595800932762212903/100000000000000000000)
  directionLo := (437408748104228500509/100000000000000000000)
  directionHi := (43740874810422850051/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree079.table
  base := (8166414712762208299843928452926393502637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-102875934119184849562245176948040000000000000)
      constant := (1669534508458300205633170430056021549500358837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree079.table
  base := (1633277030429913047042368929098023109417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-188149860512110904054966510133924000000000000)
      constant := (3101543665756838107735443063420697622968342553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437408748104228500509/100000000000000000000)
  centralHi := (43740874810422850051/10000000000000000000)
  directionLo := (55025465077519415069/12500000000000000000)
  directionHi := (440203720620155320553/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree080.table
  base := (1805434264951836852494612886341651725591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-20851178132472918632045466679920000000000000)
      constant := (343289765605130843982971008091774636138262191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree080.table
  base := (282098294203409969938265599500700927249/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-953357087341423995874578616431600000000000000)
      constant := (15942590506692015531627683375286781056191098912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55025465077519415069/12500000000000000000)
  centralHi := (440203720620155320553/100000000000000000000)
  directionLo := (221490529355967665757/50000000000000000000)
  directionHi := (88596211742387066303/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree081.table
  base := (990834674871482084478859711557269071549/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-7042389813702955783880632656744000000000000)
      constant := (117600768819632029533387123980664304570065966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree081.table
  base := (9908324036724222741910006688980430316827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-107329430235810385719369409132620000000000000)
      constant := (1820384634896245617991049354564928099254067027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221490529355967665757/50000000000000000000)
  centralHi := (88596211742387066303/20000000000000000000)
  directionLo := (55717636501390096763/12500000000000000000)
  directionHi := (89148218402224154821/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree082.table
  base := (10809940513925679687669604822750979563841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-107015803748724080356191646302720000000000000)
      constant := (1812222620040479231718952370515015297845550441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree082.table
  base := (10809920604348919284764249939093158424163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-978572656903162947074070747955560000000000000)
      constant := (16830331941205010220685702484463471745551231667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55717636501390096763/12500000000000000000)
  centralHi := (89148218402224154821/20000000000000000000)
  directionLo := (224242070003035879207/50000000000000000000)
  directionHi := (89696828001214351683/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree083.table
  base := (2932988052039738746792906354115868648873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-108395760291903823954173802754280000000000000)
      constant := (1861082090191433058173232026856261497422874692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree083.table
  base := (11731934754360200413161348830351942151497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-991180441684032422673816813717540000000000000)
      constant := (17283201179610408907722011828069398613824393273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224242070003035879207/50000000000000000000)
  centralHi := (89696828001214351683/20000000000000000000)
  directionLo := (451210512473618142559/100000000000000000000)
  directionHi := (2820065702960113391/625000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree084.table
  base := (6337190734867110735788681983406764950449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-36591905611694522517385319735280000000000000)
      constant := (636863313935537045410636381540347330424078566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree084.table
  base := (12674366168130518316495014077639092842707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-111532025162766877585951431053280000000000000)
      constant := (1971341046869294928481098844002979280483880907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451210512473618142559/100000000000000000000)
  centralHi := (2820065702960113391/625000000000000000)
  directionLo := (226960254943692978381/50000000000000000000)
  directionHi := (453920509887385956763/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree085.table
  base := (1363722798070853241683664289397307789847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (957)
      previous := (726)
      next := (0)
      square := (18817589225178321790665769794000000000000)
      linear := (-1307713804450156601766330772440000000000000)
      constant := (23067602047753457193714461316755576183693182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree085.table
  base := (170465182067373034435672394214044600413/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2754000000000000000000000000000000000000000
      center := (8514)
      previous := (6633)
      next := (0)
      square := (169358303026604896115991928146000000000000)
      linear := (-11957600132303192633803634649900000000000000)
      constant := (214199254838634181513214688920973830636299216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226960254943692978381/50000000000000000000)
  centralHi := (453920509887385956763/100000000000000000000)
  directionLo := (456614423804311936071/100000000000000000000)
  directionHi := (57076802975538992009/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree086.table
  base := (14620491461007949727551649409123102132819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-112535629921443054748120272108960000000000000)
      constant := (2011550786220258920888562517702089188647462219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree086.table
  base := (14620479699035060750505408988939636019533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1029003796026640849473055011003480000000000000)
      constant := (18677802892206725352906353954442447939581247997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456614423804311936071/100000000000000000000)
  centralHi := (57076802975538992009/12500000000000000000)
  directionLo := (28705783576922096447/6250000000000000000)
  directionHi := (459292537230753543153/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree087.table
  base := (7812085831685677537342916328539394186253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-37971862154874266115367476186840000000000000)
      constant := (687667925882376715242194997726767309518962702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree087.table
  base := (7812080675332678756316522153623274176509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-115734620089723369452533452973940000000000000)
      constant := (2128296456608841050637886088373558272266199818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28705783576922096447/6250000000000000000)
  centralHi := (459292537230753543153/100000000000000000000)
  directionLo := (230977562484747892601/50000000000000000000)
  directionHi := (461955124969495785203/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree088.table
  base := (665930734759671452749293996237695750361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-23059108601560508388816917002416000000000000)
      constant := (423021029554108125490987868082639233233444805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree088.table
  base := (8324129663369970755839913256598230875463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1054219365588379800672547142527440000000000000)
      constant := (19637532308571841348211714288297655973127426734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230977562484747892601/50000000000000000000)
  centralHi := (461955124969495785203/100000000000000000000)
  directionLo := (464602453948859171323/100000000000000000000)
  directionHi := (116150613487214792831/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree089.table
  base := (442319534593926918800245397393846583713/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-23335099910196457108413348292728000000000000)
      constant := (433570979217120924093389255267923159713900104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree089.table
  base := (17692773455269559541808167909676136300501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1066827150369249276272293208289420000000000000)
      constant := (20126395485457444602023120342847618674658427909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464602453948859171323/100000000000000000000)
  centralHi := (116150613487214792831/25000000000000000000)
  directionLo := (467234783535024440193/100000000000000000000)
  directionHi := (233617391767512220097/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree090.table
  base := (18757710535005677209554458665672423887013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-39351818698054009713349632638400000000000000)
      constant := (740417674047743145128178343363137991510040271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree090.table
  base := (4689425895741522762286671213587054041207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-119937215016679861319115474894600000000000000)
      constant := (2291250848505339733681068637703159710244717628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467234783535024440193/100000000000000000000)
  centralHi := (233617391767512220097/50000000000000000000)
  directionLo := (469852365828608427609/100000000000000000000)
  directionHi := (46985236582860842761/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree091.table
  base := (9921527834362788841884267760593118753587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-119435412637341772738031054366760000000000000)
      constant := (2275299525542829834177943872914165403756159574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree091.table
  base := (9921524786392727200611770754521153058509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1092042719930988227471785339813380000000000000)
      constant := (21122118758635615444596673272604381343893274362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469852365828608427609/100000000000000000000)
  centralHi := (46985236582860842761/10000000000000000000)
  directionLo := (118113861486612734257/25000000000000000000)
  directionHi := (472455445946450937029/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree092.table
  base := (10474408323567262348100611521914050944907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-120815369180521516336013210818320000000000000)
      constant := (2329994405926034175549722213102436893015406214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree092.table
  base := (1047440565090419402585315089266725379933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-220930100942371540614306281115072000000000000)
      constant := (4325795769768540226577238189256307097675406388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118113861486612734257/25000000000000000000)
  centralHi := (472455445946450937029/100000000000000000000)
  directionLo := (237522131144752047219/50000000000000000000)
  directionHi := (475044262289504094439/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree093.table
  base := (22074993346588515128311950602177616232027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-40731775241233753311331789089960000000000000)
      constant := (795112554323748135796182008813967993273167409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree093.table
  base := (5518747164852907351418543844947924582473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-124139809943636353185697496815260000000000000)
      constant := (2460204211619970523768185553349648207356049092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237522131144752047219/50000000000000000000)
  centralHi := (475044262289504094439/100000000000000000000)
  directionLo := (477619046797652847307/100000000000000000000)
  directionHi := (119404761699413211827/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree094.table
  base := (23221585655773058467599772716517376302243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-123575282266881003531977523721440000000000000)
      constant := (2441329296388931539871400353739821695762134043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree094.table
  base := (2322158154568880903041544829522470001457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-225973214854719330854204707419864000000000000)
      constant := (4532139184701601597125752372248015000528213826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477619046797652847307/100000000000000000000)
  centralHi := (119404761699413211827/25000000000000000000)
  directionLo := (120045006298059374777/25000000000000000000)
  directionHi := (480180025192237499109/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree095.table
  base := (48777186948276251637745625482457116357/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-24991047762012149425991936034600000000000000)
      constant := (499593861183512989568378224768187095964455700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree095.table
  base := (762143433440193177122245553045500317839/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1142473859054466129870769602861300000000000000)
      constant := (23185552903507748325286517074875997742089380832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120045006298059374777/25000000000000000000)
  centralHi := (480180025192237499109/100000000000000000000)
  directionLo := (60340927150874500019/12500000000000000000)
  directionHi := (482727417206996000153/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree096.table
  base := (5115203342108641090951693724052570005333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-8422346356882699381862789108304000000000000)
      constant := (170350512754672544019808146586497578194623711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree096.table
  base := (25576013550223275745576925530327335325331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-128342404870592845052279518735920000000000000)
      constant := (2635156538072279030427139861804221399181185931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60340927150874500019/12500000000000000000)
  centralHi := (482727417206996000153/100000000000000000000)
  directionLo := (6065767960101184149/1250000000000000000)
  directionHi := (485261436808094731921/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree097.table
  base := (26783855282083596968873085354950665071791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-127715151896420234325923993076120000000000000)
      constant := (2613194452380866051480089691957866679851728391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree097.table
  base := (13391926255436392405865766244892818895681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1167689428616205081070261734385260000000000000)
      constant := (24253263739175300814574630401537481995057993058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/1250000000000000000)
  centralHi := (485261436808094731921/100000000000000000000)
  directionLo := (121945573100967838967/25000000000000000000)
  directionHi := (487782292403871355869/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree098.table
  base := (2801210911307311471968570622545115361603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-25819021687919995584781229905536000000000000)
      constant := (534355917780607770507434316978767690111058806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree098.table
  base := (14006053341538826838450596232374978761273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1180297213397074556670007800147240000000000000)
      constant := (24796117591467901242547223765400171755645279314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121945573100967838967/25000000000000000000)
  centralHi := (487782292403871355869/100000000000000000000)
  directionLo := (245145093522435807569/50000000000000000000)
  directionHi := (490290187044871615139/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree099.table
  base := (29260778134161834435627792419602617498877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-43491688327593240507296101993080000000000000)
      constant := (910337700235409136812672702718315469371526359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree099.table
  base := (14630388001693209577447450981827869386499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-132544999797549336918861540656580000000000000)
      constant := (2816107822004775250670721516343558576548567798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245145093522435807569/50000000000000000000)
  centralHi := (490290187044871615139/100000000000000000000)
  directionLo := (492785318614723477307/100000000000000000000)
  directionHi := (123196329653680869327/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree100.table
  base := (7632465570392622049269605846222275908457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-131855021525959465119870462430800000000000000)
      constant := (2790894987624541849323695247384096558551586628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree100.table
  base := (3816232551648815845443789225042677954901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1205512782958813507869499931671200000000000000)
      constant := (25899822157528561203169501661332192385970220072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492785318614723477307/100000000000000000000)
  centralHi := (123196329653680869327/25000000000000000000)
  directionLo := (495267880012356415671/100000000000000000000)
  directionHi := (61908485001544551959/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree101.table
  base := (31819361496425663726051455805875056269217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-133234978069139208717852618882360000000000000)
      constant := (2851425249504852423859161043817841021356233417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree101.table
  base := (3181935985814962569606383255314999499377/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-243624113547936596693849199486636000000000000)
      constant := (5292134573730519962381956488579019646561832386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495267880012356415671/100000000000000000000)
  centralHi := (61908485001544551959/12500000000000000000)
  directionLo := (248869029663020349423/50000000000000000000)
  directionHi := (497738059326040698847/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree102.table
  base := (2070579732761384667926322388792372556867/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1595)
      previous := (1210)
      next := (0)
      square := (31362648708630536317776282990000000000000)
      linear := (-2639508521810175535604603437920000000000000)
      constant := (57109880121672295144415546469094576006403472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree102.table
  base := (662585485753856004610878118663252124263/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306000000000000000000000000000000000000000
      center := (946)
      previous := (737)
      next := (0)
      square := (18817589225178321790665769794000000000000)
      linear := (-1608795232053009750416983089144000000000000)
      constant := (35330094810759841197547159012090775750122390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248869029663020349423/50000000000000000000)
  centralHi := (497738059326040698847/100000000000000000000)
  directionLo := (7815563124995172971/1562500000000000000)
  directionHi := (100039207999938214029/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree103.table
  base := (34459604914120691283773686074273168616237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-135994891155498695913816931785480000000000000)
      constant := (2974430897593924914103399116014424511570832437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree103.table
  base := (3445960365458537369512901379287169783301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-248667227460284386933747625791428000000000000)
      constant := (5520074228231776153919855588052444714914586218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7815563124995172971/1562500000000000000)
  centralHi := (100039207999938214029/20000000000000000000)
  directionLo := (502642000991850946351/100000000000000000000)
  directionHi := (31415125061990684147/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree104.table
  base := (4476293627363862374842091467565038125803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-137374847698678439511799088237040000000000000)
      constant := (3036906283547659704952013609954053313321708824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree104.table
  base := (35810347914552361351219488468135884828733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1255943922082291410268484194719120000000000000)
      constant := (28179218700398973454591006710583552927955810797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502642000991850946351/100000000000000000000)
  centralHi := (31415125061990684147/6250000000000000000)
  directionLo := (505076116927747066137/100000000000000000000)
  directionHi := (252538058463873533069/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree105.table
  base := (37181507994230725546739981737191126331563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-46251601413952727703260414896200000000000000)
      constant := (1033343347983736588972609522125144706529465121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree105.table
  base := (1487260281038035414846833476849068663333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-28190037930292464130405116899580000000000000)
      constant := (639201449043927520978476289282072137966645665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505076116927747066137/100000000000000000000)
  centralHi := (252538058463873533069/50000000000000000000)
  directionLo := (507498558244780203993/100000000000000000000)
  directionHi := (253749279122390101997/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree106.table
  base := (38573081798434774262830901781797690547627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-140134760785037926707763401140160000000000000)
      constant := (3163802178696255423275302443609815793114377827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree106.table
  base := (3857308094948492770530709646598769483089/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-256231898328806072293595265248616000000000000)
      constant := (5870982131994459050279138450214213189659260802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507498558244780203993/100000000000000000000)
  centralHi := (253749279122390101997/50000000000000000000)
  directionLo := (254954745665897491979/50000000000000000000)
  directionHi := (509909491331794983959/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree107.table
  base := (9996267598066253426036584117292784325071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-141514717328217670305745557591720000000000000)
      constant := (3228222687680686534241548174448354128118038684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree107.table
  base := (7997013929591342002173835496339761253093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-258753455284979967413544478401012000000000000)
      constant := (5990351011702976216691627376357115471173654037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254954745665897491979/50000000000000000000)
  centralHi := (509909491331794983959/100000000000000000000)
  directionLo := (512309078662450840037/100000000000000000000)
  directionHi := (256154539331225420019/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree108.table
  base := (41417473738598221819049143893491958642931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-47631557957132471301242571347760000000000000)
      constant := (1097763856935981866420085850931337528143421177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree108.table
  base := (10354368271512443816318409994893726309667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-145152784578418812518607606418560000000000000)
      constant := (3394955377975308110864123462571034328525775468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512309078662450840037/100000000000000000000)
  centralHi := (256154539331225420019/50000000000000000000)
  directionLo := (128674369730749162633/25000000000000000000)
  directionHi := (514697478922996650533/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree109.table
  base := (10717572950556322190421418537575272274957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-144274630414577157501709870494840000000000000)
      constant := (3359008827986453723622365235245293132748652628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree109.table
  base := (8574058246027904284161935725050397018429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-263796569197327757653442904705804000000000000)
      constant := (6232688137794770537003550570612026743804404461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128674369730749162633/25000000000000000000)
  centralHi := (514697478922996650533/100000000000000000000)
  directionLo := (129268711783683351603/25000000000000000000)
  directionHi := (517074847134733406413/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree110.table
  base := (8868704909931632516569155645344619175433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-29130917391551380219938405389280000000000000)
      constant := (685074891825821696841595124843941354475301233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree110.table
  base := (44343524048127519050796945516690596434403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1331590630767508263866960589291000000000000000)
      constant := (31778281919351728010730901687509210171932939827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129268711783683351603/25000000000000000000)
  centralHi := (517074847134733406413/100000000000000000000)
  directionLo := (129860333692858088511/25000000000000000000)
  directionHi := (103888266954286470809/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree111.table
  base := (1145929298724019785045829334366798034317/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-9802302900062442979844945559864000000000000)
      constant := (232825897610189614005026512552632111166022712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree111.table
  base := (11459292877324111427903157357560472887351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-149355379505375304385189628339220000000000000)
      constant := (3599902454688037463759310142061349159919999804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129860333692858088511/25000000000000000000)
  centralHi := (103888266954286470809/20000000000000000000)
  directionLo := (521797089871960283877/100000000000000000000)
  directionHi := (260898544935980141939/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree112.table
  base := (473512339696009069436428923443805259517/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-29682900008823277659131267969904000000000000)
      constant := (712010168595649294288268701527594749600074340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree112.table
  base := (9470246716836580221154010487718546512499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46818000000000000000000000000000000000000000
      center := (144738)
      previous := (112761)
      next := (0)
      square := (2879091151452283233971862778482000000000000)
      linear := (-271361240065849443013290544162992000000000000)
      constant := (6605192241361194287352511196517691455311089091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521797089871960283877/100000000000000000000)
  centralHi := (260898544935980141939/50000000000000000000)
  directionLo := (104828451429669786223/20000000000000000000)
  directionHi := (131035564287087232779/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree113.table
  base := (48885710582319918391773512704250849925101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-149794456587296131893638496301080000000000000)
      constant := (3628361595529213673592092882520596460655187701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree113.table
  base := (48885710244465738846377073384322960501817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1369413985110116690666198786576940000000000000)
      constant := (33658799262529661083746437667264106182387034153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104828451429669786223/20000000000000000000)
  centralHi := (131035564287087232779/25000000000000000000)
  directionLo := (105295395617906346303/20000000000000000000)
  directionHi := (131619244522382932879/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree114.table
  base := (10088120351803710339561376811676525196343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5423)
      previous := (4114)
      next := (0)
      square := (106633005609343823480439362166000000000000)
      linear := (-10078294208698391699441376850176000000000000)
      constant := (246488048115510640315180680250507547345229381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree114.table
  base := (50440601462867871063225723796632350433771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-153557974432331796251771650259880000000000000)
      constant := (3810848473191652973870193110960680743478238371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105295395617906346303/20000000000000000000)
  centralHi := (131619244522382932879/25000000000000000000)
  directionLo := (528801391060958361403/100000000000000000000)
  directionHi := (132200347765239590351/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree115.table
  base := (26007953736328092911625041889888289301421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-152554369673655619089602809204200000000000000)
      constant := (3766928221518251609527075379596198880945992042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree115.table
  base := (52015907213069778431955421366881776410141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1394629554671855641865690918100900000000000000)
      constant := (34942472194775504852154500105471585503984990669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528801391060958361403/100000000000000000000)
  centralHi := (132200347765239590351/25000000000000000000)
  directionLo := (531115631400285518207/100000000000000000000)
  directionHi := (4149340870314730611/781250000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree116.table
  base := (10722325539432422151252453021360315281071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16269)
      previous := (12342)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-30786865243367072537516993131152000000000000)
      constant := (767436818963635954249878073521870180046065671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree116.table
  base := (13402906867408299151543747447163267991933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1407237339452725117465436983862880000000000000)
      constant := (35593307070086061015630052941583539761692638388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531115631400285518207/100000000000000000000)
  centralHi := (4149340870314730611/781250000000000000)
  directionLo := (133354957877332801061/25000000000000000000)
  directionHi := (106683966301866240849/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree117.table
  base := (55227762407357168467470126236119452430817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-51771427586671702095189040702440000000000000)
      constant := (1302696113855651033286751736602195565257518339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree117.table
  base := (11045552441586731154260859237199241564759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-31552113871857657623670734436108000000000000)
      constant := (805558686312891356474864226144197227309938159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133354957877332801061/25000000000000000000)
  centralHi := (106683966301866240849/20000000000000000000)
  directionLo := (133928530235617326287/25000000000000000000)
  directionHi := (535714120942469305149/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree118.table
  base := (3554019473680277646100242410709224667439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-156694239303194849883549278558880000000000000)
      constant := (3979640961701219255232949186048715093760141424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree118.table
  base := (56864311404100727654478581161291842527087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1432452909014464068664929115386840000000000000)
      constant := (36912973636198872073931520657448720741716579583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133928530235617326287/25000000000000000000)
  centralHi := (535714120942469305149/100000000000000000000)
  directionLo := (26899931324581572641/5000000000000000000)
  directionHi := (537998626491631452821/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree119.table
  base := (58521275188147837386658023805999753516257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4785)
      previous := (3630)
      next := (0)
      square := (94087946125891608953328848970000000000000)
      linear := (-9298482108610270204795966765320000000000000)
      constant := (238343644421153223195557529131797962287987321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree119.table
  base := (58521275034964987713937359665531126643259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (42570)
      previous := (33165)
      next := (0)
      square := (846791515133024480579959640730000000000000)
      linear := (-85003570223254914368510304773460000000000000)
      constant := (2210694430935292414954110187644166361387767643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26899931324581572641/5000000000000000000)
  centralHi := (537998626491631452821/100000000000000000000)
  directionLo := (540273472268073983019/100000000000000000000)
  directionHi := (27013673613403699151/5000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree120.table
  base := (60198653212257546631208192047495836763311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-53151384129851445693171197154000000000000000)
      constant := (1374897107294191109723651617097178890473790637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree120.table
  base := (30099326539005416371435239157760205792391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-161963164286244779984935694101200000000000000)
      constant := (4250737328072926691862858765938668590532017982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540273472268073983019/100000000000000000000)
  centralHi := (27013673613403699151/5000000000000000000)
  directionLo := (108507755956211839061/20000000000000000000)
  directionHi := (271269389890529597653/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree121.table
  base := (30948222814490765670631485080970710124653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-160834108932734080677495747913560000000000000)
      constant := (4198189061812299327035672088640369634068444906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree121.table
  base := (30948222755667204318060168861323271757351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1470276263357072495464167312672780000000000000)
      constant := (38937465515955232270821453523852242937135659118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108507755956211839061/20000000000000000000)
  centralHi := (271269389890529597653/50000000000000000000)
  directionLo := (272397334006796028619/50000000000000000000)
  directionHi := (544794668013592057239/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree122.table
  base := (31807326208351128829394896291103362687657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-162214065475913824275477904365120000000000000)
      constant := (4272335174892555582353887004246959692701191714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree122.table
  base := (63614652313606002060216130929856887661609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1482884048137941971063913378434760000000000000)
      constant := (39624294015297339926963828961105859883270605081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272397334006796028619/50000000000000000000)
  centralHi := (544794668013592057239/100000000000000000000)
  directionLo := (547041253495345927861/100000000000000000000)
  directionHi := (273520626747672963931/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree123.table
  base := (8169159194297253923572721364259699572941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-54531340673031189291153353605560000000000000)
      constant := (1449043220356204216174622160465985276237918776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree123.table
  base := (32676636732018167684614134918681869087561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (80410)
      previous := (62645)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-166165759213201271851517716021860000000000000)
      constant := (4479680161132889666086587719708993082993492322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547041253495345927861/100000000000000000000)
  centralHi := (273520626747672963931/50000000000000000000)
  directionLo := (549278650372903772897/100000000000000000000)
  directionHi := (274639325186451886449/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree124.table
  base := (33556154510754179429003318885142167926693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-164973978562273311471442217268240000000000000)
      constant := (4422572520287148741503093992619069557554656986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree124.table
  base := (33556154471173139077819965425831760168491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1508099617699680922263405509958720000000000000)
      constant := (41015947820176519310558273749177151347568411638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549278650372903772897/100000000000000000000)
  centralHi := (274639325186451886449/50000000000000000000)
  directionLo := (551506970477434673709/100000000000000000000)
  directionHi := (55150697047743467371/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree125.table
  base := (68891758798102836359241132421568580526121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-166353935105453055069424373719800000000000000)
      constant := (4498663752496168821247521236753499877948440721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree125.table
  base := (68891758728739552896915097334215110023609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1520707402480550397863151575720700000000000000)
      constant := (41720773124775465813775736163002891510542663081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551506970477434673709/100000000000000000000)
  centralHi := (55150697047743467371/10000000000000000000)
  directionLo := (69215790423739895549/12500000000000000000)
  directionHi := (553726323389919164393/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree126.table
  base := (8836452858081641922980196010406733838241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-55911297216210932889135510057120000000000000)
      constant := (1525134452548310575102228728158101105902039576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree126.table
  base := (7069162280387806761599021407215941256869/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-34073670828031552743619947588504000000000000)
      constant := (942924385856448024652013243441785326418232538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69215790423739895549/12500000000000000000)
  centralHi := (553726323389919164393/100000000000000000000)
  directionLo := (22237472660161241559/4000000000000000000)
  directionHi := (1085814094734435623/195312500000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree127.table
  base := (72511901202107706971241727262703728066677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-169113848191812542265388686622920000000000000)
      constant := (4652791335683884374834156104083132396701426877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree127.table
  base := (72511901148859556490716969041420243073229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1545922972042289349062643707244660000000000000)
      constant := (43148420536028122056622183288637896470101217661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22237472660161241559/4000000000000000000)
  centralHi := (1085814094734435623/195312500000000000)
  directionLo := (279069277543388864217/50000000000000000000)
  directionHi := (111627711017355545687/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree128.table
  base := (74352593791848877174047842362303101554929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (81345)
      previous := (61710)
      next := (0)
      square := (1599495084140157352206590432490000000000000)
      linear := (-170493804734992285863370843074480000000000000)
      constant := (4730827686564602199892759806058590367144370329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree128.table
  base := (37176296872598625467413619679670174864927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (723690)
      previous := (563805)
      next := (0)
      square := (14395455757261416169859313892410000000000000)
      linear := (-1558530756823158824662389773006640000000000000)
      constant := (43871242641806591889784547675715438246826152286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell024.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279069277543388864217/50000000000000000000)
  centralHi := (111627711017355545687/20000000000000000000)
  directionLo := (280165821168498065793/50000000000000000000)
  directionHi := (560331642336996131587/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree129.table
  base := (19053425153918011972687521152839479163221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (27115)
      previous := (20570)
      next := (0)
      square := (533165028046719117402196810830000000000000)
      linear := (-57291253759390676487117666508680000000000000)
      constant := (1603170803413245013606823408589367313738050428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree129.table
  base := (15242740114960267940718933445536626591913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5202000000000000000000000000000000000000000
      center := (16082)
      previous := (12529)
      next := (0)
      square := (319899016828031470441318086498000000000000)
      linear := (-34914189813422851116936351972636000000000000)
      constant := (991112526232269027053330884586978765765565713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell024.Kernel129
