import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell144.Parameters
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch000_049
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch050_099
import ForestUnimodality.BinomialMassData.Q7977_15052.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree000.table
  base := (1355071531273601285777274937/25000000000000000000000000)
  polynomial :=
    { denominator := 602080000000000000000000000000000000000000000
      center := (3732261)
      previous := (0)
      next := (3312075)
      square := (87074455291147636941673227614400000000000000)
      linear := (-399222863540416899397200720585600000000000000)
      constant := (32634458701968394485631267762758400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree000.table
  base := (1355071531273601285777274937/25000000000000000000000000)
  polynomial :=
    { denominator := 150520000000000000000000000000000000000000000
      center := (933309)
      previous := (0)
      next := (827775)
      square := (21768613822786909235418306903600000000000000)
      linear := (-99805715885104224849300180146400000000000000)
      constant := (8158614675492098621407816940689600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree001.table
  base := (162427972306677066883965029406508981267361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-1849481397873736196918382403624882200000000000000)
      constant := (74488162529147567315683761568477475148687310208288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree001.table
  base := (64959889493523499736162381767960023546009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-462393025107832785593382494975911800000000000000)
      constant := (18618904593579980087951899273315639998109334310420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49910142343749052697/100000000000000000000)
  directionHi := (24955071171874526349/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree002.table
  base := (12725994012184138757503500169968842501477/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-2196687160244883601405098495686151600000000000000)
      constant := (48091570526017808267912172127940933871156049820928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree002.table
  base := (50888255500022738623765064682835303564881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-549217141340018373078848412060920400000000000000)
      constant := (12019482968470832936240436057880094862320278798224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49910142343749052697/100000000000000000000)
  centralHi := (24955071171874526349/50000000000000000000)
  directionLo := (35291800101250801621/50000000000000000000)
  directionHi := (70583600202501603243/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree003.table
  base := (67176394793037761089950142401947853054041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-2543892922616031005891814587747421000000000000000)
      constant := (33654969459966398783157964653915410516086374173728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree003.table
  base := (134299177012264226092218837823873712333069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-636041257572203960564314329145929000000000000000)
      constant := (8410969800083823133220252758747697430174565314644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35291800101250801621/50000000000000000000)
  centralHi := (70583600202501603243/100000000000000000000)
  directionLo := (43223451176184082413/50000000000000000000)
  directionHi := (86446902352368164827/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree004.table
  base := (18692314723025331465343088045940417220229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-2891098684987178410378530679808690400000000000000)
      constant := (25830340546998685726869987011898874641516228696080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree004.table
  base := (5838731348610954786533672020203394098839/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-722865373804389548049780246230937600000000000000)
      constant := (6455613655639218688832315913165965988042428402624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43223451176184082413/50000000000000000000)
  centralHi := (86446902352368164827/100000000000000000000)
  directionLo := (19964056937499621079/20000000000000000000)
  directionHi := (24955071171874526349/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree005.table
  base := (68232915446943199769992510222499596132503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-3238304447358325814865246771869959800000000000000)
      constant := (21738221161444011008975191965733973044937821968112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree005.table
  base := (2131280886521049016046830660209809270929/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-809689490036575135535246163315946200000000000000)
      constant := (5433307221683347466862650269393393390967542656128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19964056937499621079/20000000000000000000)
  centralHi := (24955071171874526349/25000000000000000000)
  directionLo := (446409884189254231/400000000000000000)
  directionHi := (111602471047313557751/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree006.table
  base := (12949513679732351056050381246873120623051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-3585510209729473219351962863931229200000000000000)
      constant := (19822406382424662118688657485673454638106397159616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree006.table
  base := (25886736182761495290834350404666824168721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-896513606268760723020712080400954800000000000000)
      constant := (4954953691689394984613604894217141451378990990792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446409884189254231/400000000000000000)
  centralHi := (111602471047313557751/100000000000000000000)
  directionLo := (61127190865930836383/50000000000000000000)
  directionHi := (122254381731861672767/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree007.table
  base := (20211974825568499747906008516926257479433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-3932715972100620623838678955992498600000000000000)
      constant := (19237128170130585754278813550611180382531129733664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree007.table
  base := (8080892704101665416639019443246577820497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-983337722500946310506177997485963400000000000000)
      constant := (4809130978050635101419791268591200237197783679860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61127190865930836383/50000000000000000000)
  centralHi := (122254381731861672767/100000000000000000000)
  directionLo := (26409964908278878879/20000000000000000000)
  directionHi := (33012456135348598599/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree008.table
  base := (16032342181007174599380241479511353136913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-4279921734471768028325395048053768000000000000000)
      constant := (19518858290280899460494324913950638730795782985504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree008.table
  base := (6409729312122960963737922574043006648153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1070161838733131897991643914570972000000000000000)
      constant := (4879991041070386505281181366612700548119400357140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26409964908278878879/20000000000000000000)
  centralHi := (33012456135348598599/25000000000000000000)
  directionLo := (28233440081000641297/20000000000000000000)
  directionHi := (70583600202501603243/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree009.table
  base := (25584829210300779762559605520485261429337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-4627127496842915432812111140115037400000000000000)
      constant := (20410350733149835064344250383521174277827495647248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree009.table
  base := (5114225840069838788600950927065200563473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1156985954965317485477109831655980600000000000000)
      constant := (5103252814511127664345245857355843504953458138740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28233440081000641297/20000000000000000000)
  centralHi := (70583600202501603243/50000000000000000000)
  directionLo := (37432606757811789523/25000000000000000000)
  directionHi := (149730427031247158093/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree010.table
  base := (10171245573986566068835582143154865152377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-4974333259214062837298827232176306800000000000000)
      constant := (21766176474098463796943140786916576304355810294816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree010.table
  base := (1270651113720610776321505875461133396541/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1243810071197503072962575748740989200000000000000)
      constant := (5442581666076078599705691372757771016900132827456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37432606757811789523/25000000000000000000)
  centralHi := (149730427031247158093/100000000000000000000)
  directionLo := (157829728149461506419/100000000000000000000)
  directionHi := (7891486407473075321/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree011.table
  base := (319301305643704316224076515635988754153/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-5321539021585210241785543324237576200000000000000)
      constant := (23501917141079922479591188753943850498974745485600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree011.table
  base := (15954178229925187652692479674422054767937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1330634187429688660448041665825997800000000000000)
      constant := (5876888335645904255680645861867383716364974805412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157829728149461506419/100000000000000000000)
  centralHi := (7891486407473075321/5000000000000000000)
  directionLo := (82766607693722433387/50000000000000000000)
  directionHi := (6621328615497794671/4000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree012.table
  base := (3057081599133937688385949651147033782179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-5668744783956357646272259416298845600000000000000)
      constant := (25566771662761351959717893628790947601079285008064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree012.table
  base := (2443671655465652443854538112631050132017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1417458303661874247933507582911006400000000000000)
      constant := (6393482357747053859241288700091381690336660617460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82766607693722433387/50000000000000000000)
  centralHi := (6621328615497794671/4000000000000000000)
  directionLo := (43223451176184082413/25000000000000000000)
  directionHi := (172893804704736329653/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree013.table
  base := (1123875683019852846777967409054881200859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-6015950546327505050758975508360115000000000000000)
      constant := (27928733746424562072899003048425528360373057301888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree013.table
  base := (8981794872544435038634642784816797829117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1504282419894059835418973499996015000000000000000)
      constant := (6984368159581299175165683534913637390196519363092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43223451176184082413/25000000000000000000)
  centralHi := (172893804704736329653/100000000000000000000)
  directionLo := (179953577386093656899/100000000000000000000)
  directionHi := (1799535773860936569/1000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree014.table
  base := (96237550442980424471663140430725236987/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-6363156308698652455245691600421384400000000000000)
      constant := (30566529322567175885140188358054068424860194102272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree014.table
  base := (1230130248938809695083986212154112261019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1591106536126245422904439417081023600000000000000)
      constant := (7644230763012359280338568789070231773220023044220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179953577386093656899/100000000000000000000)
  centralHi := (1799535773860936569/1000000000000000000)
  directionLo := (46686663193856879669/25000000000000000000)
  directionHi := (186746652775427518677/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree015.table
  base := (916720567894665213750179772579717317637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-6710362071069799859732407692482653800000000000000)
      constant := (33465196775307770929436567099262635400407862441792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree015.table
  base := (3658925531426558853123722601371118863031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1677930652358431010389905334166032200000000000000)
      constant := (8369331777939440431955185416088682324278427248956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46686663193856879669/25000000000000000000)
  centralHi := (186746652775427518677/100000000000000000000)
  directionLo := (48325287526045423641/25000000000000000000)
  directionHi := (38660230020836338913/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree016.table
  base := (732524443174556017178434011582883403369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-7057567833440947264219123784543923200000000000000)
      constant := (36613635957797645702256928119493258767968006699552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree016.table
  base := (1457643487831803894391423285569948827507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1764754768590616597875371251251040800000000000000)
      constant := (9156897270024241479356469713247174946875403874732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48325287526045423641/25000000000000000000)
  centralHi := (38660230020836338913/20000000000000000000)
  directionLo := (19964056937499621079/10000000000000000000)
  directionHi := (199640569374996210791/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree017.table
  base := (-484348561532355201850900238013964616361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-7404773595812094668705839876605192600000000000000)
      constant := (40003225788902085411705173973950251143006929199856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree017.table
  base := (-245618168740538776726519077206827373243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1851578884822802185360837168336049400000000000000)
      constant := (10004772545743962906632709794914433436528424335464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19964056937499621079/10000000000000000000)
  centralHi := (199640569374996210791/100000000000000000000)
  directionLo := (205784788672889928727/100000000000000000000)
  directionHi := (25723098584111241091/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree018.table
  base := (-1105972639728097559260671572516144695221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-7751979358183242073192555968666462000000000000000)
      constant := (43627025473197107955737509888110944173390948724832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree018.table
  base := (-2218344108147186181773294972392494053721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-1938403001054987772846303085421058000000000000000)
      constant := (10911222691924321993297002111778421099471262244604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205784788672889928727/100000000000000000000)
  centralHi := (25723098584111241091/12500000000000000000)
  directionLo := (827151564873065663/390625000000000000)
  directionHi := (211750800607504809729/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree019.table
  base := (-748613135825582787471505952139359530501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-8099185120554389477679272060727731400000000000000)
      constant := (47479297443489504593076065050006904405957614826480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree019.table
  base := (-749800377980928502745158760181822001041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2025227117287173360331769002506066600000000000000)
      constant := (11874813449644195153948291872814004819746825281420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (827151564873065663/390625000000000000)
  centralHi := (211750800607504809729/100000000000000000000)
  directionLo := (108776633367066191207/50000000000000000000)
  directionHi := (43510653346826476483/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree020.table
  base := (-254951773286464030481587421022640448053/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-8446390882925536882165988152789000800000000000000)
      constant := (51555210090348586938617345574091981197386815693760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree020.table
  base := (-2552267172689134051400920319902935242669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2112051233519358947817234919591075200000000000000)
      constant := (12894336975597040561417461346067256986942007591512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108776633367066191207/50000000000000000000)
  centralHi := (43510653346826476483/20000000000000000000)
  directionLo := (223204942094627115501/100000000000000000000)
  directionHi := (111602471047313557751/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree021.table
  base := (-787255179431723369287932296784295446203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-8793596645296684286652704244850270200000000000000)
      constant := (55850642964051660578656017906314244058036894296704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree021.table
  base := (-3151563882549983288329306034434483512823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2198875349751544535302700836676083800000000000000)
      constant := (13968763185993198794667155753807719777245701223304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223204942094627115501/100000000000000000000)
  centralHi := (111602471047313557751/50000000000000000000)
  directionLo := (114358502618125356257/50000000000000000000)
  directionHi := (45743401047250142503/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree022.table
  base := (-7355726269636885701103991482766462848997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-9140802407667831691139420336911539600000000000000)
      constant := (60362052016417555011679970306813672801415695992112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree022.table
  base := (-1840106115567676984656871531957983910303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2285699465983730122788166753761092400000000000000)
      constant := (15097206089638763188852963591853330850893258860688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114358502618125356257/50000000000000000000)
  centralHi := (45743401047250142503/20000000000000000000)
  directionLo := (14631207389009452387/6250000000000000000)
  directionHi := (234099318224151238193/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree023.table
  base := (-2071405565359324774631242579279821234079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-9488008170038979095626136428972809000000000000000)
      constant := (65086371334516909423885980844513988170531779241536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree023.table
  base := (-8289956308979604578946509704311960532947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2372523582215915710273632670846101000000000000000)
      constant := (16278899232151060885951826083569756865528561647828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14631207389009452387/6250000000000000000)
  centralHi := (234099318224151238193/100000000000000000000)
  directionLo := (239360633985176685763/100000000000000000000)
  directionHi := (59840158496294171441/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree024.table
  base := (-9099482594769915779566941986531277594027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-9835213932410126500112852521034078400000000000000)
      constant := (70020938085221357340722581932875806567722628630992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree024.table
  base := (-4551737969797349840772392933588850899247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2459347698448101297759098587931109600000000000000)
      constant := (17513176936374705087228806495062602358006884058056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239360633985176685763/100000000000000000000)
  centralHi := (59840158496294171441/25000000000000000000)
  directionLo := (61127190865930836383/25000000000000000000)
  directionHi := (244508763463723345533/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree025.table
  base := (-9807544005364631256809115236594513201903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-10182419694781273904599568613095347800000000000000)
      constant := (75163433006003800221222362024317339993663158374288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree025.table
  base := (-4905609698272332642178476352173353640131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2546171814680286885244564505016118200000000000000)
      constant := (18799459425946971126672989281216869986271838862888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61127190865930836383/25000000000000000000)
  centralHi := (244508763463723345533/100000000000000000000)
  directionLo := (249550711718745263487/100000000000000000000)
  directionHi := (1949614935302697371/781250000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree026.table
  base := (-2604685242221376930736902118312632277343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-10529625457152421309086284705156617200000000000000)
      constant := (80511831877898965939383919482484304080549967938112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree026.table
  base := (-10422120332373143874343588211995987595373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2632995930912472472730030422101126800000000000000)
      constant := (20137240692748637974320606118978368453310458807852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249550711718745263487/100000000000000000000)
  centralHi := (1949614935302697371/781250000000000000)
  directionLo := (127246394868484974263/50000000000000000000)
  directionHi := (254492789736969948527/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree027.table
  base := (-5470441952584233471132525498209342653877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-10876831219523568713573000797217886600000000000000)
      constant := (86064365151069452823958931192957341646800181593184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree027.table
  base := (-10943988239985208291578564049548465513361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2719820047144658060215496339186135400000000000000)
      constant := (21526078401822345100680633027620141643560545927964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127246394868484974263/50000000000000000000)
  centralHi := (254492789736969948527/100000000000000000000)
  directionLo := (259340707057104494479/100000000000000000000)
  directionHi := (3241758838213806181/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree028.table
  base := (-11380809521884021170266589912206187606521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-11224036981894716118059716889279156000000000000000)
      constant := (91819483882538972077275012141459029230335314207216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree028.table
  base := (-1422957353163977028265583389920554888271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2806644163376843647700962256271144000000000000000)
      constant := (22965585374163225852860515274548556278665808710432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259340707057104494479/100000000000000000000)
  centralHi := (3241758838213806181/1250000000000000000)
  directionLo := (264099649082788788791/100000000000000000000)
  directionHi := (33012456135348598599/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree029.table
  base := (-1174450886418852231861210155525754172443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-11571242744265863522546432981340425400000000000000)
      constant := (97775830724917114507450931617306698736770316341280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree029.table
  base := (-11747122084450573345139931065371782232003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2893468279609029235186428173356152600000000000000)
      constant := (24455422332343074483890990835340794288054561245972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264099649082788788791/100000000000000000000)
  centralHi := (33012456135348598599/12500000000000000000)
  directionLo := (67193585517157752593/25000000000000000000)
  directionHi := (268774342068631010373/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree030.table
  base := (-6018618542930050582960720636516751688343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-11918448506637010927033149073401694800000000000000)
      constant := (103932215056353970989216949804890781817384889281056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree030.table
  base := (-1504954012351064568835001476664522013613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-2980292395841214822671894090441161200000000000000)
      constant := (25995291681639237392482681568739214483456627820896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67193585517157752593/25000000000000000000)
  centralHi := (268774342068631010373/100000000000000000000)
  directionLo := (273369108099651167397/100000000000000000000)
  directionHi := (136684554049825583699/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree031.table
  base := (-12263607974433065593339739276029657410743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-12265654269008158331519865165462964200000000000000)
      constant := (110287591564670087236252315387289309589078427270928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree031.table
  base := (-6132900790073450354802185666346791952143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3067116512073400410157360007526169800000000000000)
      constant := (27584932154939363952368377551795274131798521662664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273369108099651167397/100000000000000000000)
  centralHi := (136684554049825583699/50000000000000000000)
  directionLo := (138943955942649820681/50000000000000000000)
  directionHi := (277887911885299641363/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree032.table
  base := (-2485535121616897907843763359605594804939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-12612860031379305736006581257524233600000000000000)
      constant := (116841041746951437986276110442452022737323338024720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree032.table
  base := (-621484177167796813443602775124548861143/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3153940628305585997642825924611178400000000000000)
      constant := (29224114186740234578050056281608136966196606946640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138943955942649820681/50000000000000000000)
  centralHi := (277887911885299641363/100000000000000000000)
  directionLo := (282334400810006412971/100000000000000000000)
  directionHi := (70583600202501603243/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree033.table
  base := (-12533005062796866141955495184564502314083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-12960065793750453140493297349585503000000000000000)
      constant := (123591757889943464137191704901329355649557098239568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree033.table
  base := (-12534842025873891487415580396715965022819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3240764744537771585128291841696187000000000000000)
      constant := (30912635907552056447072437009365145986115176414356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282334400810006412971/100000000000000000000)
  centralHi := (70583600202501603243/25000000000000000000)
  directionLo := (143355969695648393361/50000000000000000000)
  directionHi := (286711939391296786723/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree034.table
  base := (-49151303711825882768314571263532127739/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-13307271556121600544980013441646772400000000000000)
      constant := (130539029173177542406025434624904775949436160958464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree034.table
  base := (-786525839667957733438141289529005302247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3327588860769957172613757758781195600000000000000)
      constant := (32650319669162899827098663947041328789170329616448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143355969695648393361/50000000000000000000)
  centralHi := (286711939391296786723/100000000000000000000)
  directionLo := (36377954883910275589/12500000000000000000)
  directionHi := (291023639071282204713/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree035.table
  base := (-1572453088405624448146498275291657213817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-13654477318492747949466729533708041800000000000000)
      constant := (137682229595549419766326787262782170430222114550656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree035.table
  base := (-3145289960597855586099284604212632899983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3414412977002142760099223675866204200000000000000)
      constant := (34437009025913812119974295531081148724220489965968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36377954883910275589/12500000000000000000)
  centralHi := (291023639071282204713/100000000000000000000)
  directionLo := (295272384091477857953/100000000000000000000)
  directionHi := (147636192045738928977/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree036.table
  base := (-12526112952304504019836501827720975280511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-14001683080863895353953445625769311200000000000000)
      constant := (145020807472693657581692662179564888182930269338256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree036.table
  base := (-1565939418495127942163707569436985295519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3501237093234328347584689592951212800000000000000)
      constant := (36272566108793407695111063442604215707677952553248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295272384091477857953/100000000000000000000)
  centralHi := (147636192045738928977/50000000000000000000)
  directionLo := (59892170812498863237/20000000000000000000)
  directionHi := (149730427031247158093/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree037.table
  base := (-6212172928281804818307278440794726819023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-14348888843235042758440161717830580600000000000000)
      constant := (152554276290394285167413554766957524872131660963616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree037.table
  base := (-12425626450559386512432988345201192036847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3588061209466513935070155510036221400000000000000)
      constant := (38156869338638046117132221834590681352027169011428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59892170812498863237/20000000000000000000)
  centralHi := (149730427031247158093/50000000000000000000)
  directionLo := (303591543730407304599/100000000000000000000)
  directionHi := (1517957718652036523/500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree038.table
  base := (-12276218339296857317344918777691475848219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-14696094605606190162926877809891850000000000000000)
      constant := (160282206730616599916690713387673163179076809775824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree038.table
  base := (-6138693623150085142867158958531650766389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3674885325698699522555621427121230000000000000000)
      constant := (40089811432563440766539893924350635966391617922072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303591543730407304599/100000000000000000000)
  centralHi := (1517957718652036523/500000000000000000)
  directionLo := (153833390176990755091/50000000000000000000)
  directionHi := (307666780353981510183/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree039.table
  base := (-377606361916704468723276894817771269947/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-15043300367977337567413593901953119400000000000000)
      constant := (168204219712987409016890634678959121978723399785984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree039.table
  base := (-604223507099504334080513004462531472037/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3761709441930885110041087344206238600000000000000)
      constant := (42071297664317512484263062383034107240050984459760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153833390176990755091/50000000000000000000)
  centralHi := (307666780353981510183/100000000000000000000)
  directionLo := (155844369518245986537/50000000000000000000)
  directionHi := (12467549561459678923/4000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree040.table
  base := (-5923689926234747925245610896267446019139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-15390506130348484971900309994014388800000000000000)
      constant := (176319980316705207571793134358228449845459664816288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree040.table
  base := (-11848352682042200127207891489548881567569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3848533558163070697526553261291247200000000000000)
      constant := (44101244344785885277916564039019512412968952163356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155844369518245986537/50000000000000000000)
  centralHi := (12467549561459678923/4000000000000000000)
  directionLo := (157829728149461506419/50000000000000000000)
  directionHi := (315659456298923012839/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree041.table
  base := (-11569453965750563306984052952073242716773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-15737711892719632376387026086075658200000000000000)
      constant := (184629192466672026222305199076514469380289602965808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree041.table
  base := (-2892585250419783953255347799420111927929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-3935357674395256285012019178376255800000000000000)
      constant := (46179577493586602246216179815166317434625752639984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157829728149461506419/50000000000000000000)
  centralHi := (315659456298923012839/100000000000000000000)
  directionLo := (319580842134983084329/100000000000000000000)
  directionHi := (31958084213498308433/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree042.table
  base := (-11250781800806808652471499773677707425683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-16084917655090779780873742178136927600000000000000)
      constant := (193131594283673605873851073427499174606116380473168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree042.table
  base := (-2250318069746313744851567508957176039659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4022181790627441872497485095461264400000000000000)
      constant := (48306231676701586424463490794813769570313557152580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319580842134983084329/100000000000000000000)
  centralHi := (31958084213498308433/10000000000000000000)
  directionLo := (323454690750463953899/100000000000000000000)
  directionHi := (3234546907504639539/1000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree043.table
  base := (-5446193138920358091798881515806510343869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-16432123417461927185360458270198197000000000000000)
      constant := (201826954012142895456665509157846253657628139076448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree043.table
  base := (-2723280763949773542406007326365947340487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4109005906859627459982951012546273000000000000000)
      constant := (50481148988521299897046915209572631902017656603152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323454690750463953899/100000000000000000000)
  centralHi := (3234546907504639539/1000000000000000000)
  directionLo := (327282690158296584293/100000000000000000000)
  directionHi := (163641345079148292147/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree044.table
  base := (-5247586556045530218533329799847482967677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-16779329179833074589847174362259466400000000000000)
      constant := (210715066450786344206066542269503175842498308562784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree044.table
  base := (-2623961073169032106703807657832844917107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4195830023091813047468416929631281600000000000000)
      constant := (52704278159616692144972389575896739475567582222672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327282690158296584293/100000000000000000000)
  centralHi := (163641345079148292147/50000000000000000000)
  directionLo := (82766607693722433387/25000000000000000000)
  directionHi := (331066430774889733549/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree045.table
  base := (-2514986158519979169776898174624322647123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-17126534942204221994333890454320735800000000000000)
      constant := (219795749821431369018045719284510444513847501197632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree045.table
  base := (-5030277942218699317785546934526268817517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4282654139323998634953882846716290200000000000000)
      constant := (54975573774073496872529513520866063413836232957016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82766607693722433387/25000000000000000000)
  centralHi := (331066430774889733549/100000000000000000000)
  directionLo := (83701853285485168313/25000000000000000000)
  directionHi := (334807413141940673253/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree046.table
  base := (-1917482384545552273545562449212049033849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-17473740704575369398820606546382005200000000000000)
      constant := (229068843020114989345308575209833082132552915161520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree046.table
  base := (-4793984221164629442846262040764352696263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4369478255556184222439348763801298800000000000000)
      constant := (57294995582390347381536599076306043513162482012424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83701853285485168313/25000000000000000000)
  centralHi := (334807413141940673253/100000000000000000000)
  directionLo := (33850705488005924339/10000000000000000000)
  directionHi := (338507054880059243391/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree047.table
  base := (-9078205465526176852681331846946202345683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-17820946466946516803307322638443274600000000000000)
      constant := (238534203201886274113456166988368650810280916793168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree047.table
  base := (-4539356010852129406590717116859577995999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4456302371788369809924814680886307400000000000000)
      constant := (59662507897806157842286943954588222235463782689352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33850705488005924339/10000000000000000000)
  centralHi := (338507054880059243391/100000000000000000000)
  directionLo := (342166696965594143733/100000000000000000000)
  directionHi := (171083348482797071867/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree048.table
  base := (-1706576906324665194061776756002996586587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-18168152229317664207794038730504544000000000000000)
      constant := (248191703657214751773654828849678587506200395743760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree048.table
  base := (-4266672746445240644080925934350544165929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4543126488020555397410280597971316000000000000000)
      constant := (62078079065527749299232703031830087914947850543992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342166696965594143733/100000000000000000000)
  centralHi := (171083348482797071867/50000000000000000000)
  directionLo := (69157521881894531861/20000000000000000000)
  directionHi := (172893804704736329653/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree049.table
  base := (-7951945419245674788758638186217958061693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-18515357991688811612280754822565813400000000000000)
      constant := (258041231943432243769140663093976888444434235102128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree049.table
  base := (-1590472957289244584256027970994076305099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4629950604252740984895746515056324600000000000000)
      constant := (64541680995713050774938357518218734855418051965380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69157521881894531861/20000000000000000000)
  centralHi := (172893804704736329653/50000000000000000000)
  directionLo := (174685498203121684441/50000000000000000000)
  directionHi := (349370996406243368883/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree050.table
  base := (-1467165743558382731244020840112827340163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-18862563754059959016767470914627082800000000000000)
      constant := (268082688239413229080569153027203211488637714596240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree050.table
  base := (-7336210153155687841942988331160354106183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4716774720484926572381212432141333200000000000000)
      constant := (67053288752260035417392321005379438179026419100292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174685498203121684441/50000000000000000000)
  centralHi := (349370996406243368883/100000000000000000000)
  directionLo := (176459000506254008107/50000000000000000000)
  directionHi := (70583600202501603243/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree051.table
  base := (-3342462853358115236091118402900862445107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-19209769516431106421254187006688352200000000000000)
      constant := (278315983895826547253308000790331849727259013021344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree051.table
  base := (-6685272560896721857869074720410226717521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4803598836717112159866678349226341800000000000000)
      constant := (69612880190483807754621641586239654386406349515804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176459000506254008107/50000000000000000000)
  centralHi := (70583600202501603243/20000000000000000000)
  directionLo := (356429709406269753703/100000000000000000000)
  directionHi := (44553713675783719213/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree052.table
  base := (-2999791998781341683687932863823502009153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-19556975278802253825740903098749621600000000000000)
      constant := (288741040156860834862125644104540944112113727140576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree052.table
  base := (-1499974833687899596782039075125845641611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-4890422952949297747352144266311350400000000000000)
      constant := (72220435637656916064610017593429812871149996923856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356429709406269753703/100000000000000000000)
  centralHi := (44553713675783719213/12500000000000000000)
  directionLo := (179953577386093656899/50000000000000000000)
  directionHi := (359907154772187313799/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree053.table
  base := (-165003515996074226129658736581787955961/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (264990531)
      previous := (0)
      next := (235157325)
      square := (6182286325671482222858799160622400000000000000)
      linear := (-375550585682517004343917343222847000000000000000)
      constant := (5648260132687093635145817994308669472068320254464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree053.table
  base := (-2640199566545107157071063746183337924963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10686920000000000000000000000000000000000000000
      center := (66264939)
      previous := (0)
      next := (58772025)
      square := (1545571581417870555714699790155600000000000000)
      linear := (-93910322060027987449766229875403000000000000000)
      constant := (1412753539833219553391952812410339397452590883208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179953577386093656899/50000000000000000000)
  centralHi := (359907154772187313799/100000000000000000000)
  directionLo := (181675660426062911359/50000000000000000000)
  directionHi := (363351320852125822719/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree054.table
  base := (-4526785875884736103511775658610091042991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-20251386803544548634714335282872160400000000000000)
      constant := (310166162302429895413455099607322828916613778792336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree054.table
  base := (-1131761585133963821305603800714886863587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5064071185413668922323076100481367600000000000000)
      constant := (77579370569664421645763909852665072199131650140752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181675660426062911359/50000000000000000000)
  centralHi := (363351320852125822719/100000000000000000000)
  directionLo := (366763145195585018299/100000000000000000000)
  directionHi := (3667631451955850183/1000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree055.table
  base := (-1869924151325254002713177880687557488419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-20598592565915696039201051374933429800000000000000)
      constant := (321166110637332145533207774844142156848786685350048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree055.table
  base := (-3740084948473824558772215445293087284583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5150895301645854509808542017566376200000000000000)
      constant := (80330720693331270259560290275426620143074214501892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366763145195585018299/100000000000000000000)
  centralHi := (3667631451955850183/1000000000000000000)
  directionLo := (37014352214044090991/10000000000000000000)
  directionHi := (370143522140440909911/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree056.table
  base := (-1459758511695204918786099932710624305943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-20945798328286843443687767466994699200000000000000)
      constant := (332357582820630406853565365162030511815434861300256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree056.table
  base := (-1459865992432988786402511839139460520059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5237719417878040097294007934651384800000000000000)
      constant := (83129975689550711776939279846133939395737093360232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37014352214044090991/10000000000000000000)
  centralHi := (370143522140440909911/100000000000000000000)
  directionLo := (373493305550855037353/100000000000000000000)
  directionHi := (186746652775427518677/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree057.table
  base := (-2065985322064324128490393333564273945659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-21293004090657990848174483559055968600000000000000)
      constant := (343740535061388088561339245086093529193324747898064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree057.table
  base := (-2066180547403849030822791398045086161999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5324543534110225684779473851736393400000000000000)
      constant := (85977124621138963632817068464721462466306131128676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373493305550855037353/100000000000000000000)
  centralHi := (186746652775427518677/50000000000000000000)
  directionLo := (376813311336101360983/100000000000000000000)
  directionHi := (47101663917012670123/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree058.table
  base := (-294856305126497887203040190331251570579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-21640209853029138252661199651117238000000000000000)
      constant := (355314928385873391331756430985138706778861499657536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree058.table
  base := (-294900621827578365416092996537782650189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5411367650342411272264939768821402000000000000000)
      constant := (88872157754326590787217041980592770624608894048944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376813311336101360983/100000000000000000000)
  centralHi := (47101663917012670123/12500000000000000000)
  directionLo := (47513039971420435739/12500000000000000000)
  directionHi := (380104319771363485913/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree059.table
  base := (-64997463892738550964062637866442930809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-21987415615400285657147915743178507400000000000000)
      constant := (367080728098986241488050054439140530901186912209856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree059.table
  base := (-260150785247847354229305613824739886679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5498191766574596859750405685906410600000000000000)
      constant := (91815066424185455643973823942360372012294338044996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47513039971420435739/12500000000000000000)
  centralHi := (380104319771363485913/100000000000000000000)
  directionLo := (11980221176225156433/3125000000000000000)
  directionHi := (383367077639205005857/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree060.table
  base := (692184415336569426627284260521585621299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-22334621377771433061634631835239776800000000000000)
      constant := (379037903307224428870441174188234561388729021432496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree060.table
  base := (43252396519188692453782053089417360723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5585015882806782447235871602991419200000000000000)
      constant := (94805842915435526545732742762614661804119785099968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11980221176225156433/3125000000000000000)
  centralHi := (383367077639205005857/100000000000000000000)
  directionLo := (386602300208363389129/100000000000000000000)
  directionHi := (38660230020836338913/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree061.table
  base := (209622018555005721893248529965806009513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-22681827140142580466121347927301046200000000000000)
      constant := (391186426495957558062131933029487952702687720025216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree061.table
  base := (67073743532383340043813262280931443521/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5671839999038968034721337520076427800000000000000)
      constant := (97844480356823943933867137804972430096767131504900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386602300208363389129/100000000000000000000)
  centralHi := (38660230020836338913/10000000000000000000)
  directionLo := (19490533653236051349/5000000000000000000)
  directionHi := (389810673064721026981/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree062.table
  base := (2694277159432948118179529345974136296553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-23029032902513727870608064019362315600000000000000)
      constant := (403526273154656612003793304136900892858411593559312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree062.table
  base := (2694156881980400646816386438055035451823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5758664115271153622206803437161436400000000000000)
      constant := (100930972627488548237693065898333499433195220152348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19490533653236051349/5000000000000000000)
  centralHi := (389810673064721026981/100000000000000000000)
  directionLo := (196496426903865172647/50000000000000000000)
  directionHi := (78598570761546069059/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree063.table
  base := (748798211267979846540394467925360609963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-23376238664884875275094780111423585000000000000000)
      constant := (416057421444495005330356520560452143206091533099760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree063.table
  base := (3743881942583647012055998393551280783347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5845488231503339209692269354246445000000000000000)
      constant := (104065314273910095284506452745980875009234583622572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196496426903865172647/50000000000000000000)
  centralHi := (78598570761546069059/20000000000000000000)
  directionLo := (198074736812091591593/50000000000000000000)
  directionHi := (396149473624183183187/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree064.table
  base := (4826031937713768926586733512896284303833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-23723444427256022679581496203484854400000000000000)
      constant := (428779851903408598712453343985022871443429162044432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree064.table
  base := (1206483242118011848204887654348335049057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-5932312347735524797177735271331453600000000000000)
      constant := (107247500436225281493195005351655033746612326570128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198074736812091591593/50000000000000000000)
  centralHi := (396149473624183183187/100000000000000000000)
  directionLo := (19964056937499621079/5000000000000000000)
  directionHi := (399281138749992421581/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree065.table
  base := (1485080809269997429987976953574127637749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-24070650189627170084068212295546123800000000000000)
      constant := (441693547184289878394611264401477134444448183653184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree065.table
  base := (5940233484314028093384237916371015344459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6019136463967710384663201188416462200000000000000)
      constant := (110477526782819629205489165720596239400916530614284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19964056937499621079/5000000000000000000)
  centralHi := (399281138749992421581/100000000000000000000)
  directionLo := (100597107957393583781/25000000000000000000)
  directionHi := (3219107454636594681/800000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree066.table
  base := (7086796696811467391815582980531690635889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-24417855951998317488554928387607393200000000000000)
      constant := (454798491822506281286461846232351877813158491283856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree066.table
  base := (3543357657845372004556191495974045128511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6105960580199895972148667105501470800000000000000)
      constant := (113755389452247969127522965075545546889066739826872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100597107957393583781/25000000000000000000)
  centralHi := (3219107454636594681/800000000000000000)
  directionLo := (405471913181464745569/100000000000000000000)
  directionHi := (40547191318146474557/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree067.table
  base := (8265391456609174315579079030903893852799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-24765061714369464893041644479668662600000000000000)
      constant := (468094672029383893440352190218389510561669119408496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree067.table
  base := (8265317678242178268750169440487125131989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6192784696432081559634133022586479400000000000000)
      constant := (117081085001643059676337182287821042761772446184564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405471913181464745569/100000000000000000000)
  centralHi := (40547191318146474557/10000000000000000000)
  directionLo := (204266060988977422607/50000000000000000000)
  directionHi := (81706424395590969043/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree068.table
  base := (2369013310877708916166826973555232983677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-25112267476740612297528360571729932000000000000000)
      constant := (481582075508693627781582313347142586012527395930432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree068.table
  base := (1895197273657731215365331370378448287761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6279608812664267147119598939671488000000000000000)
      constant := (120454610360871842384056181554239179234249127832180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204266060988977422607/50000000000000000000)
  centralHi := (81706424395590969043/20000000000000000000)
  directionLo := (205784788672889928727/50000000000000000000)
  directionHi := (82313915469155971491/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree069.table
  base := (10718733651884247275569009191193561181917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-25459473239111759702015076663791201400000000000000)
      constant := (495260691293524563305387046332631267515014551423568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree069.table
  base := (535933652169402583270802671450609877271/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6366432928896452734605064856756496600000000000000)
      constant := (123875962791785715756307626909574055106218129503920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205784788672889928727/50000000000000000000)
  centralHi := (82313915469155971491/20000000000000000000)
  directionLo := (103646194848555933563/25000000000000000000)
  directionHi := (414584779394223734253/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree070.table
  base := (11993389503209746909725880707787182660707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-25806679001482907106501792755852470800000000000000)
      constant := (509130509601234530617831927163594689585151692471728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree070.table
  base := (1499166822829594022946188956442062552743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6453257045128638322090530773841505200000000000000)
      constant := (127345139851987549430371488388854360322573193394144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103646194848555933563/25000000000000000000)
  centralHi := (414584779394223734253/100000000000000000000)
  directionLo := (417578210176405699893/100000000000000000000)
  directionHi := (208789105088202849947/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree071.table
  base := (3324995569160417767460590747718792147513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31910240000000000000000000000000000000000000000
      center := (197809833)
      previous := (0)
      next := (175539975)
      square := (4614946130430824757908681063563200000000000000)
      linear := (-368364574138789500154767730252306200000000000000)
      constant := (7368894671893472899018247566241404537724902093248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree071.table
  base := (265998650354151049765280360825341346203/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7977560000000000000000000000000000000000000000
      center := (49465377)
      previous := (0)
      next := (43872075)
      square := (1153736532607706189477170265890800000000000000)
      linear := (-92113819174096111402478826632767800000000000000)
      constant := (1843128723416975857996567124297434425549076023400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417578210176405699893/100000000000000000000)
  centralHi := (208789105088202849947/50000000000000000000)
  directionLo := (84110066917796170543/20000000000000000000)
  directionHi := (105137583647245213179/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree072.table
  base := (14638477602381657491108217643182675115603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-26501090526225201915475224939975009600000000000000)
      constant := (537443719816216246053291024793095150440144528270512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree072.table
  base := (2927686505332096713859276836681886494073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6626905277593009497061462608011522400000000000000)
      constant := (134426959379621043742304999729195179839897823566740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84110066917796170543/20000000000000000000)
  centralHi := (105137583647245213179/25000000000000000000)
  directionLo := (423501601215009619457/100000000000000000000)
  directionHi := (211750800607504809729/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree073.table
  base := (4002211202703781828933876916822407876269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-26848296288596349319961941032036279000000000000000)
      constant := (551887096987982731662976603468743842121203608285504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree073.table
  base := (2001100497935106952150689005374858010297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6713729393825195084546928525096531000000000000000)
      constant := (138039598168356647687279502312683693153857896326176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423501601215009619457/100000000000000000000)
  centralHi := (211750800607504809729/50000000000000000000)
  directionLo := (136458381796583363/32000000000000000)
  directionHi := (13326013847322594043/3125000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree074.table
  base := (1088191033198226819942921124479835678569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-27195502050967496724448657124097548400000000000000)
      constant := (566521647018540268621285790126895854661996279849216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree074.table
  base := (17411019557107954723771356806483889291341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6800553510057380672032394442181539600000000000000)
      constant := (141700054180762343119875588280593534772570715186516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136458381796583363/32000000000000000)
  centralHi := (13326013847322594043/3125000000000000000)
  directionLo := (107335819641331645943/25000000000000000000)
  directionHi := (429343278565326583773/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree075.table
  base := (4711272083545847105450937056173594414259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-27542707813338644128935373216158817800000000000000)
      constant := (581347364373127893202113007764752921681825260785344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree075.table
  base := (18845054854431310248693277523110207326859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6887377626289566259517860359266548200000000000000)
      constant := (145408326035195863240348476486240698390493446716684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107335819641331645943/25000000000000000000)
  centralHi := (429343278565326583773/100000000000000000000)
  directionLo := (432234511761840824131/100000000000000000000)
  directionHi := (108058627940460206033/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree076.table
  base := (20310918413846097951147176543857392319009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-27889913575709791533422089308220087200000000000000)
      constant := (596364244111318306114099561080578867894183509640336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree076.table
  base := (20310888102360965763206910633678994096787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-6974201742521751847003326276351556800000000000000)
      constant := (149164412498414674307762407532922396592642025108012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432234511761840824131/100000000000000000000)
  centralHi := (108058627940460206033/25000000000000000000)
  directionLo := (108776633367066191207/25000000000000000000)
  directionHi := (435106533468264764829/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree077.table
  base := (2180852730394193025936641019034310469883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-28237119338080938937908805400281356600000000000000)
      constant := (611572281822792559717677652530077784294572030436320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree077.table
  base := (21808499864633965333360893981535056843717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7061025858753937434488792193436565400000000000000)
      constant := (152968312469535703584260164916964861362326557232692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108776633367066191207/25000000000000000000)
  centralHi := (435106533468264764829/100000000000000000000)
  directionLo := (437959721636069517337/100000000000000000000)
  directionHi := (218979860818034758669/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree078.table
  base := (2917237203184485700193680960725850535363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-28584325100452086342395521492342626000000000000000)
      constant := (626971473570118554068160708816263895824933511212416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree078.table
  base := (11668936394755119650717141214022847798001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7147849974986123021974258110521574000000000000000)
      constant := (156820024965744663748141345686357022857447776177352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437959721636069517337/100000000000000000000)
  centralHi := (218979860818034758669/50000000000000000000)
  directionLo := (440794441984375286527/100000000000000000000)
  directionHi := (1721853289001465963/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree079.table
  base := (4979802772322142161157269789331044844953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-28931530862823233746882237584403895400000000000000)
      constant := (642561815837759683558988237069320325912339062164560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree079.table
  base := (12449495692472523193592366101344319177219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7234674091218308609459724027606582600000000000000)
      constant := (160719549109561668031047918046112110718914895920088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440794441984375286527/100000000000000000000)
  centralHi := (1721853289001465963/390625000000000000)
  directionLo := (88722209709427341893/20000000000000000000)
  directionHi := (221805524273568354733/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree080.table
  base := (3311482769633696178704607060187367899441/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-29278736625194381151368953676465164800000000000000)
      constant := (658343305486626963457195232193541630543521224387712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree080.table
  base := (6622960454552233010759097362067966095761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7321498207450494196945189944691591200000000000000)
      constant := (164666884117491569202293911472481561430435935097744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88722209709427341893/20000000000000000000)
  centralHi := (221805524273568354733/50000000000000000000)
  directionLo := (446409884189254231003/100000000000000000000)
  directionHi := (111602471047313557751/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree081.table
  base := (7029107534828847691480003089124549585161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-29625942387565528555855669768526434200000000000000)
      constant := (674315939713564939683123584142126819943434617741376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree081.table
  base := (28116411737265777408208342568587472407013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7408322323682679784430655861776599800000000000000)
      constant := (168662029289906691513188345244759920427264563460788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446409884189254231003/100000000000000000000)
  centralHi := (111602471047313557751/25000000000000000000)
  directionLo := (224595640546870737139/50000000000000000000)
  directionHi := (449191281093741474279/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree082.table
  base := (2977270675911661692527260607178119329149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-29973148149936675960342385860587703600000000000000)
      constant := (690479716015229833359226631106103748273466634588960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree082.table
  base := (29772690111520180390511239641055742220519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7495146439914865371916121778861608400000000000000)
      constant := (172704984002026654706737800150050372693051937230844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224595640546870737139/50000000000000000000)
  centralHi := (449191281093741474279/100000000000000000000)
  directionLo := (451955561221908142391/100000000000000000000)
  directionHi := (56494445152738517799/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree083.table
  base := (31460682148375500790945129362424858545743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-30320353912307823364829101952648973000000000000000)
      constant := (706834632155878735562425400802301096555191041769072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree083.table
  base := (786516677245293189851924144716464825633/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7581970556147050959401587695946617000000000000000)
      constant := (176795747695875073583760850554872957267163009916320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451955561221908142391/100000000000000000000)
  centralHi := (56494445152738517799/12500000000000000000)
  directionLo := (454703036748363108183/100000000000000000000)
  directionHi := (56837879593545388523/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree084.table
  base := (8295086873332804701966469275260434826069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-30667559674678970769315818044710242400000000000000)
      constant := (723380686138642161698815954803167298573639849322304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree084.table
  base := (33180333873769718382801402359583424184499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7668794672379236546887053613031625600000000000000)
      constant := (180934319873106283961634929172404799824204772081324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454703036748363108183/100000000000000000000)
  centralHi := (56837879593545388523/12500000000000000000)
  directionLo := (114358502618125356257/25000000000000000000)
  directionHi := (457434010472501425029/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree085.table
  base := (17465847460729698305463530347814869894391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-31014765437050118173802534136771511800000000000000)
      constant := (740117876179899702206331189273838006735612838786528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree085.table
  base := (34931682604851135252848473247968724158023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7755618788611422134372519530116634200000000000000)
      constant := (185120700088607096953862928058822456788167953543548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114358502618125356257/25000000000000000000)
  centralHi := (457434010472501425029/100000000000000000000)
  directionLo := (460148776208010614729/100000000000000000000)
  directionHi := (46014877620801061473/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree086.table
  base := (9178679350143829805591977023156072280971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-31361971199421265578289250228832781200000000000000)
      constant := (757046200686420573032140323832729999024984950022336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree086.table
  base := (36714706263570234323577836962364839871351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7842442904843607721857985447201642800000000000000)
      constant := (189354887944789094854682514959179371588945073673276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460148776208010614729/100000000000000000000)
  centralHi := (46014877620801061473/10000000000000000000)
  directionLo := (462847619151814507583/100000000000000000000)
  directionHi := (7231994049247101681/1562500000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree087.table
  base := (38529408648812853083485544806003211511331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-31709176961792412982775966320894050600000000000000)
      constant := (774165658234968196791158492503717481088941077999024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree087.table
  base := (38529398579592797899360774370136562938071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-7929267021075793309343451364286651400000000000000)
      constant := (193636883086496308827882116976788952362128887575996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462847619151814507583/100000000000000000000)
  centralHi := (7231994049247101681/1562500000000000000)
  directionLo := (93106163246753202237/20000000000000000000)
  directionHi := (232765408116883005593/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree088.table
  base := (40375763054297358743654709531155311244391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-32056382724163560387262682412955320000000000000000)
      constant := (791476247554101080660426961594921172759490829793264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree088.table
  base := (4037575395151426154147197742095261664093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8016091137307978896828917281371660000000000000000)
      constant := (197966685196461397794166772085372193570511124468680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93106163246753202237/20000000000000000000)
  centralHi := (232765408116883005593/50000000000000000000)
  directionLo := (14631207389009452387/3125000000000000000)
  directionHi := (93639727289660495277/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree089.table
  base := (42253775603460747589127008678156841349393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-32403588486534707791749398505016589400000000000000)
      constant := (808977967507931681795503283478951682768467486838672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree089.table
  base := (42253767375270727527166389955999094317017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8102915253540164484314383198456668600000000000000)
      constant := (202344293991250799839325339728435912182503601183492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14631207389009452387/3125000000000000000)
  centralHi := (93639727289660495277/20000000000000000000)
  directionLo := (470851341169187925571/100000000000000000000)
  directionHi := (117712835292296981393/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree090.table
  base := (44163441817062208731293200433377641653069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-32750794248905855196236114597077858800000000000000)
      constant := (826670817081631090214311505531123097971062342538576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree090.table
  base := (5520429297530897471754052668883160860807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8189739369772350071799849115541677200000000000000)
      constant := (206769709217645858316699155702789551669382803084256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470851341169187925571/100000000000000000000)
  centralHi := (117712835292296981393/25000000000000000000)
  directionLo := (236744592224192259629/50000000000000000000)
  directionHi := (473489184448384519259/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree091.table
  base := (23052378846540328671536841783800857245191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-33098000011277002600722830689139128200000000000000)
      constant := (844554795368490587473415100873702518136226927912928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree091.table
  base := (23052375486124838086135779947079780925587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8276563486004535659285315032626685800000000000000)
      constant := (211242930649412728270084366081271988660114306753624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236744592224192259629/50000000000000000000)
  centralHi := (473489184448384519259/100000000000000000000)
  directionLo := (59514051662502569217/12500000000000000000)
  directionHi := (476112413300020553737/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree092.table
  base := (48077719655736093606600151013475023621029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-33445205773648150005209546781200397600000000000000)
      constant := (862629901558371787904958318341607902688044201502416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree092.table
  base := (48077713582599372728613076313986142674131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8363387602236721246770780949711694400000000000000)
      constant := (215763958084419027548803577306944042975695227552556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59514051662502569217/12500000000000000000)
  centralHi := (476112413300020553737/100000000000000000000)
  directionLo := (239360633985176685763/50000000000000000000)
  directionHi := (478721267970353371527/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree093.table
  base := (50082324509978101834235984956097688419861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-33792411536019297409696262873261667000000000000000)
      constant := (880896134927395429914426186433280963182803195464144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree093.table
  base := (12520579755671804868835013023653549066191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8450211718468906834256246866796703000000000000000)
      constant := (220332791342059784062967524938426475460632907940464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239360633985176685763/50000000000000000000)
  centralHi := (478721267970353371527/100000000000000000000)
  directionLo := (19252639287782490339/4000000000000000000)
  directionHi := (120328995548640564619/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree094.table
  base := (325741058755323763579232171948036137919/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-34139617298390444814182978965322936400000000000000)
      constant := (899353494828735216124259018991653175408463291676160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree094.table
  base := (52118564443400200349237372347116151543907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8537035834701092421741712783881711600000000000000)
      constant := (224949430260959310582356846134992763573965336161132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19252639287782490339/4000000000000000000)
  centralHi := (120328995548640564619/25000000000000000000)
  directionLo := (241948391720574092979/50000000000000000000)
  directionHi := (483896783441148185959/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree095.table
  base := (54186451777215700611017192464579756282893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-34486823060761592218669695057384205800000000000000)
      constant := (918001980684397631364746046071074144963363227022672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree095.table
  base := (1354661182472351897921749875390920200517/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8623859950933278009227178700966720200000000000000)
      constant := (229613874696919268394755923112510839001773537179680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241948391720574092979/50000000000000000000)
  centralHi := (483896783441148185959/100000000000000000000)
  directionLo := (486463893144663674329/100000000000000000000)
  directionHi := (48646389314466367433/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree096.table
  base := (56285969359342958638056907494694780021607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-34834028823132739623156411149445475200000000000000)
      constant := (936841591977881598721418639845635339016380460345328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree096.table
  base := (11257193062848924096831229660997304960991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8710684067165463596712644618051728800000000000000)
      constant := (234326124521086411508075395117223426935843419349580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486463893144663674329/100000000000000000000)
  centralHi := (48646389314466367433/10000000000000000000)
  directionLo := (97803505385489338213/20000000000000000000)
  directionHi := (244508763463723345533/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree097.table
  base := (58417120109988411312425584768669957776743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-35181234585503887027643127241506744600000000000000)
      constant := (955872328247623344914233851282216531673714722393072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree097.table
  base := (29208558228280056498013822072903724577497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8797508183397649184198110535136737400000000000000)
      constant := (239086179618316378606952766750786963710974488935944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97803505385489338213/20000000000000000000)
  centralHi := (244508763463723345533/50000000000000000000)
  directionLo := (491557894810986981229/100000000000000000000)
  directionHi := (49155789481098698123/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree098.table
  base := (60579902208548900930283664822397012612581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-35528440347875034432129843333568014000000000000000)
      constant := (975094189081142095622871358606460560764028455779024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree098.table
  base := (3786243681823940197895887073449670816141/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8884332299629834771683576452221746000000000000000)
      constant := (243894039885712460248303532186090909412059167221056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491557894810986981229/100000000000000000000)
  centralHi := (49155789481098698123/10000000000000000000)
  directionLo := (4940852014175112227/1000000000000000000)
  directionHi := (494085201417511222701/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree099.table
  base := (62774314027984782453873516616044960807199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-35875646110246181836616559425629283400000000000000)
      constant := (994507174109811349352376610833348986912303028106096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree099.table
  base := (31387155524324624899929448103851538575713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-8971156415862020359169042369306754600000000000000)
      constant := (248749705231320548880257638286647792922136923003976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4940852014175112227/1000000000000000000)
  centralHi := (494085201417511222701/100000000000000000000)
  directionLo := (248299823081167300161/50000000000000000000)
  directionHi := (496599646162334600323/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree100.table
  base := (32500177057103172812266325347310795301521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-36222851872617329241103275517690552800000000000000)
      constant := (1014111283004188609487970494928587288323806186145568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree100.table
  base := (8125043928013570785383886350887753217183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9057980532094205946654508286391763200000000000000)
      constant := (253653175572963510291112077585341714338739359485664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248299823081167300161/50000000000000000000)
  centralHi := (496599646162334600323/100000000000000000000)
  directionLo := (19964056937499621079/4000000000000000000)
  directionHi := (1949614935302697371/390625000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree101.table
  base := (67258021167660874316892670422252004439657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-36570057634988476645589991609751822200000000000000)
      constant := (1033906515469843698673745143954207144801518694752528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree101.table
  base := (67258018738942995614275598660298102989769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9144804648326391534139974203476771800000000000000)
      constant := (258604450837200024616924862036578519539858137243844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19964056937499621079/4000000000000000000)
  centralHi := (1949614935302697371/390625000000000000)
  directionLo := (501590722787117057041/100000000000000000000)
  directionHi := (250795361393558528521/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree102.table
  base := (34773657013442279181793143640669365550661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-36917263397359624050076707701813091600000000000000)
      constant := (1053892871243632235480039132462513521683244410294688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree102.table
  base := (17386827958586726523183582569457738613049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9231628764558577121625440120561780400000000000000)
      constant := (263603530958394557525559156552726679173897591124496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501590722787117057041/100000000000000000000)
  centralHi := (250795361393558528521/50000000000000000000)
  directionLo := (504067729075047813343/100000000000000000000)
  directionHi := (15752116533595244167/3125000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree103.table
  base := (35934115826904435190257305645796971415011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-37264469159730771454563423793874361000000000000000)
      constant := (1074070350090366607405412969336173902013841196699488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree103.table
  base := (8983528709332389037574420008835036512609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9318452880790762709110906037646789000000000000000)
      constant := (268650415877886559367986485600522385949470850269472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504067729075047813343/100000000000000000000)
  centralHi := (15752116533595244167/3125000000000000000)
  directionLo := (253266311322513389103/50000000000000000000)
  directionHi := (506532622645026778207/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree104.table
  base := (37110386560316830326078354296666981488021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-37611674922101918859050139885935630400000000000000)
      constant := (1094438951799841903758713401031333195426887962737568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree104.table
  base := (74220771334259324725739316939642936850913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9405276997022948296596371954731797600000000000000)
      constant := (273745105543248271226924697808211908741861023537188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253266311322513389103/50000000000000000000)
  centralHi := (506532622645026778207/100000000000000000000)
  directionLo := (127246394868484974263/25000000000000000000)
  directionHi := (508985579473939897053/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree105.table
  base := (76604937598099409434375184173531569945277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-37958880684473066263536855977996899800000000000000)
      constant := (1114998676184178845428967271186323839372417089149008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree105.table
  base := (19151233996465404418380605126460239195137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9492101113255133884081837871816806200000000000000)
      constant := (278887599907621659025743399875940065365537022370448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127246394868484974263/25000000000000000000)
  centralHi := (508985579473939897053/100000000000000000000)
  directionLo := (255713385659215970203/50000000000000000000)
  directionHi := (511426771318431940407/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree106.table
  base := (79020724345009076923872746628364209007139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (264990531)
      previous := (0)
      next := (235157325)
      square := (6182286325671482222858799160622400000000000000)
      linear := (-722756348053664408830633435284116400000000000000)
      constant := (21429236284442449563802715421600374338009029568752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree106.table
  base := (987759036125694346034581634562182712153/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10686920000000000000000000000000000000000000000
      center := (66264939)
      previous := (0)
      next := (58772025)
      square := (1545571581417870555714699790155600000000000000)
      linear := (-180734438292213574935232146960411600000000000000)
      constant := (5359960357153321045383805324480012753361297110080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255713385659215970203/50000000000000000000)
  centralHi := (511426771318431940407/100000000000000000000)
  directionLo := (128464091463813578451/25000000000000000000)
  directionHi := (102771273171050862761/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree107.table
  base := (20367033174716511393803284628511213903841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-38653292209215361072510288162119438600000000000000)
      constant := (1156691492323557823054495458160716680771756451784256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree107.table
  base := (4073406569298079615480430231751393605181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9665749345719505059052769705986823400000000000000)
      constant := (289316002570328677459941969961131228179790578847120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128464091463813578451/25000000000000000000)
  centralHi := (102771273171050862761/20000000000000000000)
  directionLo := (64534315851958544403/12500000000000000000)
  directionHi := (20650981072626734209/4000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree108.table
  base := (83947162067508969873100211980292083983389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-39000497971586508476997004254180708000000000000000)
      constant := (1177824583794341158303598125016270814957071702923856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree108.table
  base := (83947160882881884203719445506180898582849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9752573461951690646538235623071832000000000000000)
      constant := (294601910797772118671063288648494619074020009365924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64534315851958544403/12500000000000000000)
  centralHi := (20650981072626734209/4000000000000000000)
  directionLo := (259340707057104494479/50000000000000000000)
  directionHi := (518681414114208988959/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree109.table
  base := (86457811921637124046364947703825800120857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-39347703733957655881483720346241977400000000000000)
      constant := (1199148797367880028968973379652571654226594888717328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree109.table
  base := (86457810852839976717781535697913661613769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9839397578183876234023701540156840600000000000000)
      constant := (299935623581551396188523640471464241808439127067844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259340707057104494479/50000000000000000000)
  centralHi := (518681414114208988959/100000000000000000000)
  directionLo := (13026929599302382427/2500000000000000000)
  directionHi := (521077183972095297081/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree110.table
  base := (44500040894065618323175299040509279568563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-39694909496328803285970436438303246800000000000000)
      constant := (1220664132936983253596703552164695844457291173348704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree110.table
  base := (22250020205978690715727881906999817127159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-9926221694416061821509167457241849200000000000000)
      constant := (305317140894936579493804348137839799595834654877936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13026929599302382427/2500000000000000000)
  centralHi := (521077183972095297081/100000000000000000000)
  directionLo := (523461989035557518911/100000000000000000000)
  directionHi := (8179093578680586233/1562500000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree111.table
  base := (91573971244084972001406357823622525043527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-40042115258699950690457152530364516200000000000000)
      constant := (1242370590405836029238287779962760456505419194817008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree111.table
  base := (11446746296785478593452310632259407324263/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10013045810648247408994633374326857800000000000000)
      constant := (310746462714035361912139574371207545530644860174304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523461989035557518911/100000000000000000000)
  centralHi := (8179093578680586233/1562500000000000000)
  directionLo := (105167195697866819621/20000000000000000000)
  directionHi := (262917989244667049053/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree112.table
  base := (11772434988933911932286294262387613486143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-40389321021071098094943868622425785600000000000000)
      constant := (1264268169688791528737585881971801816060219396885376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree112.table
  base := (47089739563450294391517145054641784362291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10099869926880432996480099291411866400000000000000)
      constant := (316223589017491569952283970900061272808252782297432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105167195697866819621/20000000000000000000)
  centralHi := (262917989244667049053/50000000000000000000)
  directionLo := (264099649082788788791/50000000000000000000)
  directionHi := (528199298165577577583/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree113.table
  base := (96816607452376060584747970440558643907487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-40736526783442245499430584714487055000000000000000)
      constant := (1286356870709291009359054299468597250990503380564848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree113.table
  base := (19363321348947528274723494028019861540451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10186694043112618583965565208496875000000000000000)
      constant := (321748519786215743757342590127949505920387729924380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264099649082788788791/50000000000000000000)
  centralHi := (528199298165577577583/100000000000000000000)
  directionLo := (530552090648394313437/100000000000000000000)
  directionHi := (265276045324197156719/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree114.table
  base := (1243566919559229846405669013979416965371/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-41083732545813392903917300806548324400000000000000)
      constant := (1308636693398898741432418541941584771666434249854720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree114.table
  base := (99485352926536006040628619118788996381941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10273518159344804171451031125581883600000000000000)
      constant := (327321255003144371021928828469396383156434692432116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530552090648394313437/100000000000000000000)
  centralHi := (265276045324197156719/50000000000000000000)
  directionLo := (532894495374230065691/100000000000000000000)
  directionHi := (133223623843557516423/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree115.table
  base := (102185717978543858386775447219288724972709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-41430938308184540308404016898609593800000000000000)
      constant := (1331107637696439528193609782079655317892779277245136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree115.table
  base := (102185717403006349915530712886567284991019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10360342275576989758936497042666892200000000000000)
      constant := (332941794653024721892779729745019970966375970088844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532894495374230065691/100000000000000000000)
  centralHi := (133223623843557516423/25000000000000000000)
  directionLo := (535226648728301458313/100000000000000000000)
  directionHi := (267613324364150729157/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree116.table
  base := (2622942511310557831050306190304095437843/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-41778144070555687712890732990670863200000000000000)
      constant := (1353769703547227893671823762929664948286870960298880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree116.table
  base := (104917699933434067009452966188401024975881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10447166391809175346421962959751900800000000000000)
      constant := (338610138722222558363612004201324359413726783535556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535226648728301458313/100000000000000000000)
  centralHi := (267613324364150729157/50000000000000000000)
  directionLo := (67193585517157752593/12500000000000000000)
  directionHi := (107509736827452404149/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree117.table
  base := (53840650385303593097862794936744153425207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-42125349832926835117377449082732132600000000000000)
      constant := (1376622890902379181222628568984496821018661519359456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree117.table
  base := (107681300302645212210829232479260691224471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10533990508041360933907428876836909400000000000000)
      constant := (344326287198550282725719649879284011756181305182396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67193585517157752593/12500000000000000000)
  centralHi := (107509736827452404149/20000000000000000000)
  directionLo := (539860732158280970697/100000000000000000000)
  directionHi := (269930366079140485349/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree118.table
  base := (27619129685054475548215894480181423733321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-42472555595297982521864165174793402000000000000000)
      constant := (1399667199718193846212476693807364459911363922639936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree118.table
  base := (27619129579573720017587562849822105897929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10620814624273546521392894793921918000000000000000)
      constant := (350090240071113349509297706539056575531209142240016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539860732158280970697/100000000000000000000)
  centralHi := (269930366079140485349/50000000000000000000)
  directionLo := (542162920564703020721/100000000000000000000)
  directionHi := (271081460282351510361/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree119.table
  base := (113303354188830968343495212423370931060371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-42819761357669129926350881266854671400000000000000)
      constant := (1422902629955607155859100595816526450992285241003184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree119.table
  base := (56651676904221857681820764383856769474283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10707638740505732108878360711006926600000000000000)
      constant := (355901997330172997403433471153085133045399107470616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542162920564703020721/100000000000000000000)
  centralHi := (271081460282351510361/50000000000000000000)
  directionLo := (108891074885689648021/20000000000000000000)
  directionHi := (272227687214224120053/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree120.table
  base := (58080903481154526034592628316256628854351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-43166967120040277330837597358915940800000000000000)
      constant := (1446329181579697339306182695685269403982332369450208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree120.table
  base := (23232361323878380202587307699383019588527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10794462856737917696363826628091935200000000000000)
      constant := (361761558967023564867765903113595199062077055621260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108891074885689648021/20000000000000000000)
  centralHi := (272227687214224120053/50000000000000000000)
  directionLo := (273369108099651167397/50000000000000000000)
  directionHi := (109347643239860466959/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree121.table
  base := (29762969230715152989319562064612852426967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-43514172882411424735324313450977210200000000000000)
      constant := (1469946854559245972342943792056868568892276424155072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree121.table
  base := (7440742288358952269470688942547870261139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10881286972970103283849292545176943800000000000000)
      constant := (367668924973882838214435595543361656168219351839424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273369108099651167397/50000000000000000000)
  centralHi := (109347643239860466959/20000000000000000000)
  directionLo := (549011565781239579673/100000000000000000000)
  directionHi := (274505782890619789837/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree122.table
  base := (3049339098682639236850048448798620527233/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-43861378644782572139811029543038479600000000000000)
      constant := (1493755648866345043297840088798597762749792564721280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree122.table
  base := (30493390917168709135995092850901308082877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-10968111089202288871334758462261952400000000000000)
      constant := (373624095343794046224889698028236363296393669219408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549011565781239579673/100000000000000000000)
  centralHi := (274505782890619789837/50000000000000000000)
  directionLo := (17227360643934781631/3125000000000000000)
  directionHi := (551275540605913012193/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree123.table
  base := (62463433962762560008558636760224998671579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-44208584407153719544297745635099749000000000000000)
      constant := (1517755564476045738038940661791317202801108692379232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree123.table
  base := (124926867674390591505483200335206440304271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11054935205434474458820224379346961000000000000000)
      constant := (379627070070538262994957761781988290803387555127196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17227360643934781631/3125000000000000000)
  centralHi := (551275540605913012193/100000000000000000000)
  directionLo := (553530255703439338681/100000000000000000000)
  directionHi := (276765127851719669341/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree124.table
  base := (127911788759076113459349543080658859388789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-44555790169524866948784461727161018400000000000000)
      constant := (1541946601366044510283132208159923678184679823125456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree124.table
  base := (15988973566592356065632082964903934434241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11141759321666660046305690296431969600000000000000)
      constant := (385677849148556112566838112813918448571320702295328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553530255703439338681/100000000000000000000)
  centralHi := (276765127851719669341/50000000000000000000)
  directionLo := (138943955942649820681/25000000000000000000)
  directionHi := (22231032950823971309/4000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree125.table
  base := (65464163179976258599968098282270195781207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-44902995931896014353271177819222287800000000000000)
      constant := (1566328759516402475316073812099068698035849300607456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree125.table
  base := (8183020384748554075842029774668342691911/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11228583437898845633791156213516978200000000000000)
      constant := (391776432572877786697511005934187772318911980349376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138943955942649820681/25000000000000000000)
  centralHi := (22231032950823971309/4000000000000000000)
  directionLo := (279006177618283894377/50000000000000000000)
  directionHi := (111602471047313557751/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree126.table
  base := (133976480649478335442708257924187990759429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-45250201694267161757757893911283557200000000000000)
      constant := (1590902038909294586790292797554427308815783247736016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree126.table
  base := (133976480465666434900030707242010804740429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11315407554131031221276622130601986800000000000000)
      constant := (397922820339060492336920287651029720079801903090004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279006177618283894377/50000000000000000000)
  centralHi := (111602471047313557751/20000000000000000000)
  directionLo := (560239958326282556029/100000000000000000000)
  directionHi := (56023995832628255603/10000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree127.table
  base := (27411250311463604145608744604688083460011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-45597407456638309162244610003344826600000000000000)
      constant := (1615666439528785432886016872451011635882638840148720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree127.table
  base := (137056251391686747339455410010811477744771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11402231670363216808762088047686995400000000000000)
      constant := (404117012443132539391105802562283558633022784905196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560239958326282556029/100000000000000000000)
  centralHi := (56023995832628255603/10000000000000000000)
  directionLo := (281229369560776896493/50000000000000000000)
  directionHi := (562458739121553792987/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree128.table
  base := (70083819510295949439910196552883106906783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-45944613219009456566731326095406096000000000000000)
      constant := (1640621961360628824595264819204116474593443664842464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree128.table
  base := (140167638871352029955176161697621087124909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11489055786595402396247553964772004000000000000000)
      constant := (410359008881543363325748340147426546766609742198484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell144.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281229369560776896493/50000000000000000000)
  centralHi := (562458739121553792987/100000000000000000000)
  directionLo := (564668801620012825943/100000000000000000000)
  directionHi := (70583600202501603243/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree129.table
  base := (35827660745771363856254077745026465652169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327661175260588557811516355512987200000000000000)
      linear := (-46291818981380603971218042187467365400000000000000)
      constant := (1665768604392088649514981648141163135995124128419904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7977
  qDenominator := 15052
  table := BinomialMassData.Q7977_15052.Degree129.table
  base := (71655321424311419777251143590276614791867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 566406760000000000000000000000000000000000000000
      center := (3512041767)
      previous := (0)
      next := (3114917325)
      square := (81915293815147139452879088878246800000000000000)
      linear := (-11575879902827587983733019881857012600000000000000)
      constant := (416648809651118852195750302308658656202605892364184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7977_15052.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell144.Kernel129
