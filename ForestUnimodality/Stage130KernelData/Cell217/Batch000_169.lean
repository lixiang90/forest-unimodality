import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell217.Parameters
import ForestUnimodality.BinomialMassData.Q99_179.Batch000_049
import ForestUnimodality.BinomialMassData.Q99_179.Batch050_099
import ForestUnimodality.BinomialMassData.Q99_179.Batch100_149
import ForestUnimodality.BinomialMassData.Q99_179.Batch150_199
import ForestUnimodality.BinomialMassData.Q5_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q5_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q5_9.Batch100_149
import ForestUnimodality.BinomialMassData.Q5_9.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree000.table
  base := (1593838696835902754067149109/50000000000000000000000000)
  polynomial :=
    { denominator := 223750000000000000000000000000000000000000
      center := (891)
      previous := (0)
      next := (720)
      square := (12521461760935655039422842540000000000000)
      linear := (-55052607398574854372097498525000000000000)
      constant := (7132428168340664824450492262775000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree000.table
  base := (1593838696835902754067149109/50000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (5)
      previous := (0)
      next := (4)
      square := (69952300340422653851524260000000000000)
      linear := (-307556465913826002078756975000000000000)
      constant := (39845967420897568851678727725000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree001.table
  base := (35305383535137738118874071755974198313041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-98669329224081269043289400471160000000000000)
      constant := (5705185454271504479440112198675726440740733405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree001.table
  base := (175892211607542906799132699078195013911573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-83220748719087853373377329000000000000000)
      constant := (4790659976002679114082801996111265375612471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24845199749997663293/50000000000000000000)
  directionHi := (49690399499995326587/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree002.table
  base := (106346965521518015652256933555478350192519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-118503324653403346625735183054520000000000000)
      constant := (3516605732254668746612128102427001818518501279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree002.table
  base := (52862931501122335803337183218051559575867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-50004650400394645148871575700000000000000)
      constant := (1473532899818685207453091351887392108548409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24845199749997663293/50000000000000000000)
  centralHi := (49690399499995326587/100000000000000000000)
  directionLo := (35136418446315325911/50000000000000000000)
  directionHi := (70272836892630651823/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree003.table
  base := (70056404577795814657532032653480534619111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-138337320082725424208180965637880000000000000)
      constant := (2424845633941996286418800342348289809730935551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree003.table
  base := (1391614514256339602489805717290862441187/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-6488769604582818179006054100000000000000)
      constant := (112853961232182745356694710296814683089025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/50000000000000000000)
  centralHi := (70272836892630651823/100000000000000000000)
  directionLo := (21516574145596760473/25000000000000000000)
  directionHi := (86066296582387041893/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree004.table
  base := (1998806672011371174775766270041241380421/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-158171315512047501790626748221240000000000000)
      constant := (1863257894128063485016608078636265376751731525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree004.table
  base := (12406438102767824920543011136924024042497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-33396601241048041036618699050000000000000)
      constant := (390534551441836434131185273696948649147419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21516574145596760473/25000000000000000000)
  centralHi := (86066296582387041893/100000000000000000000)
  directionLo := (99380798999990653173/100000000000000000000)
  directionHi := (49690399499995326587/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree005.table
  base := (18923930699926046769193910751393887457893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-89002655470684789686536265402300000000000000)
      constant := (783906075769156919228374068690911548038349613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree005.table
  base := (9398707904100799556671429718438065251421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-37593739261473400267710154650000000000000)
      constant := (329045375106304927446743923647827761788367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99380798999990653173/100000000000000000000)
  centralHi := (49690399499995326587/50000000000000000000)
  directionLo := (111111111111111111111/100000000000000000000)
  directionHi := (13888888888888888889/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree006.table
  base := (14907142263281235600402241961697905847331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-98919653185345828477759156693980000000000000)
      constant := (707171499808461393838017546395602601254332571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree006.table
  base := (29619568441529155844748032510578585546797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-18573723236399448666134049000000000000000)
      constant := (132117169355139588727617791531735756640391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/100000000000000000000)
  centralHi := (13888888888888888889/12500000000000000000)
  directionLo := (121716123890036914101/100000000000000000000)
  directionHi := (60858061945018457051/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree007.table
  base := (24016018773067066199087495550643015014111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-217673301800013734537964095971320000000000000)
      constant := (1343465091215041973440196371486672844067130551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree007.table
  base := (4771597023203551597267144104043362911533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-183952061209296474919572263400000000000000)
      constant := (1131023877278807309958866229045853993056955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121716123890036914101/100000000000000000000)
  centralHi := (60858061945018457051/50000000000000000000)
  directionLo := (131468439624435912057/100000000000000000000)
  directionHi := (65734219812217956029/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree008.table
  base := (19542231648186175467909823597633567553941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-237507297229335812120409878554680000000000000)
      constant := (1325994442482782529833088515943297137995823581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree008.table
  base := (970407607633815609054607968499588272023/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-50185153322749477960984521450000000000000)
      constant := (279434365879667511829566293747444416723105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/100000000000000000000)
  centralHi := (65734219812217956029/50000000000000000000)
  directionLo := (35136418446315325911/25000000000000000000)
  directionHi := (28109134757052260729/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree009.table
  base := (15925863481086745956051923451446175304587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-257341292658657889702855661138040000000000000)
      constant := (1346965994506982604040586097218466902934272067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree009.table
  base := (15808654713848003374066056351870244723137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-8056635754544420324751996600000000000000)
      constant := (42101373418485574227521187351870244723137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/25000000000000000000)
  centralHi := (28109134757052260729/20000000000000000000)
  directionLo := (1863389981249824747/1250000000000000000)
  directionHi := (149071198499985979761/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree010.table
  base := (12912275745244476114833494172840272125861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-277175288087979967285301443721400000000000000)
      constant := (1398220874259277050141423592917975159184712301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree010.table
  base := (6404038375969620924947130611846636138189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-117158858727200392846334865300000000000000)
      constant := (590617250167550879059240911519859175731103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1863389981249824747/1250000000000000000)
  centralHi := (149071198499985979761/100000000000000000000)
  directionLo := (39283710065919306911/25000000000000000000)
  directionHi := (31426968052735445529/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree011.table
  base := (10351321375821190788614096068887280483609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-297009283517302044867747226304760000000000000)
      constant := (1474948219635185897973725674840697353975315969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree011.table
  base := (10257982433710667649861907357924178709203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-251106269536102222617035553000000000000000)
      constant := (1247221950129181090359193069663952825148481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39283710065919306911/25000000000000000000)
  centralHi := (31426968052735445529/20000000000000000000)
  directionLo := (82402205412174032763/50000000000000000000)
  directionHi := (164804410824348065527/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree012.table
  base := (8146493504350913316428627040173232016911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-316843278946624122450193008888120000000000000)
      constant := (1574055854062190789343509506619310527053845351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree012.table
  base := (4031359499740377802898751635154234236817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-14883045645433536641188965300000000000000)
      constant := (74006489287219295629143084905462702710451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82402205412174032763/50000000000000000000)
  centralHi := (164804410824348065527/100000000000000000000)
  directionLo := (34426518632954816757/20000000000000000000)
  directionHi := (86066296582387041893/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree013.table
  base := (1557641068955683145509589663511112179617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-84169318593986550008159697867870000000000000)
      constant := (423347432459471780293842497635789545347108297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree013.table
  base := (6155459270820037156754434929800233158307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-284683373699505096465767197800000000000000)
      constant := (1434114737639804799869070620104606295274289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34426518632954816757/20000000000000000000)
  centralHi := (86066296582387041893/50000000000000000000)
  directionLo := (22395160411940415701/12500000000000000000)
  directionHi := (179161283295523325609/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree014.table
  base := (1138397552586407513672919018798831362121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-89127817451317069403771143513710000000000000)
      constant := (457837401980771692181373658918553355673718961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree014.table
  base := (4486435960393896567811193579773829455281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-301471925781206533390133020200000000000000)
      constant := (1551872024780718901149797608653893395292587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/12500000000000000000)
  centralHi := (179161283295523325609/100000000000000000000)
  directionLo := (11620278146306604833/6250000000000000000)
  directionHi := (185924450340905677329/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree015.table
  base := (96148387421322881273042889624833297291/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-47043158154323794399691294579775000000000000)
      constant := (248336445430558631337770640474002134714003724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree015.table
  base := (3016899976536859630360782576271793586719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-35362275318100885590499871400000000000000)
      constant := (187149160346413535726040842728815380760157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/6250000000000000000)
  centralHi := (185924450340905677329/100000000000000000000)
  directionLo := (48112522432468813709/25000000000000000000)
  directionHi := (192450089729875254837/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree016.table
  base := (884484161959824751845520157196408782487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-198089630331956216389988069610780000000000000)
      constant := (1079210033042483030903852276805370133799665967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree016.table
  base := (1715813761237149279096578637517664965357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-335049029944609407238864665000000000000000)
      constant := (1830687978584495580259501719212976954064639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/25000000000000000000)
  centralHi := (192450089729875254837/100000000000000000000)
  directionLo := (198761597999981306347/100000000000000000000)
  directionHi := (49690399499995326587/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree017.table
  base := (604941418318871273834404796161728053853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-416013256093234510362421921804920000000000000)
      constant := (2345724203910314172832849681679537928573503973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree017.table
  base := (278944880214974792833057673097067959473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-175918791013155422081615243700000000000000)
      constant := (995112933610645073629841709673620834905771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/100000000000000000000)
  centralHi := (49690399499995326587/25000000000000000000)
  directionLo := (102439382858809859/50000000000000000)
  directionHi := (204878765717619718001/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree018.table
  base := (-27260045341393958236926528606902674667/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-54480906440319573493108463048535000000000000)
      constant := (318492076744913490308546740777602462801989306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree018.table
  base := (-477679141477643586485984935308320512149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-13652819781778232632873937400000000000000)
      constant := (80088678403966559661033981064691679487851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/50000000000000000)
  centralHi := (204878765717619718001/100000000000000000000)
  directionLo := (105409255338945977733/50000000000000000000)
  directionHi := (210818510677891955467/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree019.table
  base := (-685790238462697658716862832126498721579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-227840623475939332763656743485820000000000000)
      constant := (1382252416735374538108566286041374854461887261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree019.table
  base := (-1408109674345909527825092423812298543303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-385414686189713718011962132200000000000000)
      constant := (2346728475935688930181638931557067939330819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105409255338945977733/50000000000000000000)
  centralHi := (210818510677891955467/100000000000000000000)
  directionLo := (108297714942321821187/50000000000000000000)
  directionHi := (1732763439077149139/800000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree020.table
  base := (-54092748853748510448871431935421079/244140625000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-59439405297650092888719908694375000000000000)
      constant := (374371249781733648977012233484208726823736320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree020.table
  base := (-140480787973724779605900117961308819741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-50275404783926894367040994325000000000000)
      constant := (317855311691642175363322686130089323733986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/50000000000000000000)
  centralHi := (1732763439077149139/800000000000000000)
  directionLo := (111111111111111111111/50000000000000000000)
  directionHi := (222222222222222222223/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree021.table
  base := (-1490126631564828901956205083533973126269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-247674618905261410346102526069180000000000000)
      constant := (1619475138027334813334248306919027967061214971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree021.table
  base := (-11751214246215543331177086156683123751/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3750000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (12)
      square := (209856901021267961554572780000000000000)
      linear := (-5819330421571063775842969125000000000000)
      constant := (38200215711686468235669233353958420119904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/50000000000000000000)
  centralHi := (222222222222222222223/100000000000000000000)
  directionLo := (56927504255331102129/25000000000000000000)
  directionHi := (227710017021324408517/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree022.table
  base := (-735070002097537519932344486118288434467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-515183233239844898274650834721720000000000000)
      constant := (3496127604731192234702777628091739601356214265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree022.table
  base := (-3699854783366011393387756747185725605891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-435780342434818028785059599400000000000000)
      constant := (2969180548512589302142298437825985408640943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/25000000000000000000)
  centralHi := (227710017021324408517/100000000000000000000)
  directionLo := (9322745317068013751/4000000000000000000)
  directionHi := (7283394778959385743/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree023.table
  base := (-2154601438584324298931296141992075419029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-267508614334583487928548308652540000000000000)
      constant := (1883118444259336261482844456982291911498891811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree023.table
  base := (-86611217109503472476971234240627832621/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-226284447258259732854712710900000000000000)
      constant := (1599457580748284501861940160387576212980825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9322745317068013751/4000000000000000000)
  centralHi := (7283394778959385743/3125000000000000000)
  directionLo := (238306784328080184551/100000000000000000000)
  directionHi := (29788348041010023069/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree024.table
  base := (-2444354966990560520595114112548299499969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-277425612049244526719771199944220000000000000)
      constant := (2024528553165166385950837057988479935721493271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree024.table
  base := (-196291607977579040600068737254732264993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-52150827399802322514865693800000000000000)
      constant := (382159346613242549053367252705895080125525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/100000000000000000000)
  centralHi := (29788348041010023069/12500000000000000000)
  directionLo := (243432247780073828203/100000000000000000000)
  directionHi := (60858061945018457051/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree025.table
  base := (-5419623416138276178195889071147004496347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-574685219527811131021988182471800000000000000)
      constant := (4344403950797707761535902350366378828932545773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree025.table
  base := (-1087151849338376069740344941675040471623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-486145998679922339558157066600000000000000)
      constant := (3690583078931741147301501857873869536330895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/100000000000000000000)
  centralHi := (60858061945018457051/25000000000000000000)
  directionLo := (124225998749988316467/50000000000000000000)
  directionHi := (49690399499995326587/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree026.table
  base := (-1181348107632997645593981576826845403203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-594519214957133208604433965055160000000000000)
      constant := (4652123714370205997014500255493335232179863385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree026.table
  base := (-2960365573067165312883850550791822536089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-251467275380811888241261444500000000000000)
      constant := (1976116717356945566582676908128620791525597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/50000000000000000000)
  centralHi := (49690399499995326587/20000000000000000000)
  directionLo := (31671539586087166087/12500000000000000000)
  directionHi := (253372316688697328697/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree027.table
  base := (-127081245516847039669492231824181203059/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-307176605193227643093439873819260000000000000)
      constant := (2486044100891412710038080957142495251819664525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree027.table
  base := (-6366174939377318043948023246206815324131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-19249003809012044940995878200000000000000)
      constant := (156454741583042579138246481753793184675869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31671539586087166087/12500000000000000000)
  centralHi := (253372316688697328697/100000000000000000000)
  directionLo := (129099444873580562839/50000000000000000000)
  directionHi := (258198889747161125679/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree028.table
  base := (-6764925629718132300133664310636759260273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-634187205815777363769325530221880000000000000)
      constant := (5304190492201015096988257704728007596541592807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree028.table
  base := (-3387699024102663094889483726735061141369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-268255827462513325165627266900000000000000)
      constant := (2253313771314167800583462985378153349183037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129099444873580562839/50000000000000000000)
  centralHi := (258198889747161125679/100000000000000000000)
  directionLo := (131468439624435912057/50000000000000000000)
  directionHi := (52587375849774364823/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree029.table
  base := (-142842277256606254418979561069622201957/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-327010600622549720675885656402620000000000000)
      constant := (2824170703546887498524731682037945875677394075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree029.table
  base := (-357557830375875689159194406082390753873/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-138325051751682021813905089050000000000000)
      constant := (1199801894682542935257559034428877248227145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/50000000000000000000)
  centralHi := (52587375849774364823/20000000000000000000)
  directionLo := (267590990639828788447/100000000000000000000)
  directionHi := (8362218457494649639/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree030.table
  base := (-748794841024135072075294804388327709071/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-336927598337210759467108547694300000000000000)
      constant := (3002233282680134460154337058475967959368280445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree030.table
  base := (-3747873687787979966420880281249831001563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-31671597727134973565554787700000000000000)
      constant := (283442006587476773354902954156250506995311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/100000000000000000000)
  centralHi := (8362218457494649639/3125000000000000000)
  directionLo := (272165526975908677577/100000000000000000000)
  directionHi := (136082763487954338789/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree031.table
  base := (-7804365521425116696126510969186172093717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-693689192103743596516662877971960000000000000)
      constant := (6372503927631104585389040170956985859945213603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree031.table
  base := (-1562216862045257741409647226437614032179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-586877311170130961104352001000000000000000)
      constant := (5414821485299734289396994495430922105655835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/100000000000000000000)
  centralHi := (136082763487954338789/50000000000000000000)
  directionLo := (3458305443885758993/1250000000000000000)
  directionHi := (276664435510860719441/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree032.table
  base := (-8092980177949733830346481218846491732281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-713523187533065674099108660555320000000000000)
      constant := (6752401748281857757375189116238459558405984479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree032.table
  base := (-8098762375181695449503565295684474705591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-603665863251832398028717823400000000000000)
      constant := (5737760614885372573776553337016519182949043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3458305443885758993/1250000000000000000)
  centralHi := (276664435510860719441/100000000000000000000)
  directionLo := (35136418446315325911/12500000000000000000)
  directionHi := (281091347570522607289/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree033.table
  base := (-417756970103910927474701951392404346781/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-183339295740596937920388610784670000000000000)
      constant := (1786029216843049781739763464221809861623949895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree033.table
  base := (-4180055354292003329925149250196634001407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-34469689740751879719615758100000000000000)
      constant := (337263201144537081002032268749410097995779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/12500000000000000000)
  centralHi := (281091347570522607289/100000000000000000000)
  directionLo := (57089922571845017867/20000000000000000000)
  directionHi := (35681201607403136167/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree034.table
  base := (-4295983359284572739776894734161415653717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-376595589195854914632000112861020000000000000)
      constant := (3773806643022669602274730830893574081039253603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree034.table
  base := (-8596236928592595876659678019777489661371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-637242967415235271877449468200000000000000)
      constant := (6413722596758315856635653455466007779142983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57089922571845017867/20000000000000000000)
  centralHi := (35681201607403136167/12500000000000000000)
  directionLo := (36217791140014715081/12500000000000000000)
  directionHi := (289742329120117720649/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree035.table
  base := (-8804399238484233072682362239575827388211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-773025173821031906846446008305400000000000000)
      constant := (7962860978325749469220861958742750914654331349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree035.table
  base := (-8808064053992298939545428180571942098023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-654031519496936708801815290600000000000000)
      constant := (6766690621848127201904200634124557563353379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/12500000000000000000)
  centralHi := (289742329120117720649/100000000000000000000)
  directionLo := (146986183948032810583/50000000000000000000)
  directionHi := (293972367896065621167/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree036.table
  base := (-899321858960370409555424276084575187091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-396429584625176992214445895444380000000000000)
      constant := (4194917450038861901653118780218110632152086345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree036.table
  base := (-8996361271032499082569886759886475408007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-24845187836245857249117819000000000000000)
      constant := (264060034364532153574908861240113524591993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146986183948032810583/50000000000000000000)
  centralHi := (293972367896065621167/100000000000000000000)
  directionLo := (298142396999971959521/100000000000000000000)
  directionHi := (149071198499985979761/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree037.table
  base := (-4579538357315395919892952206188611548009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-406346582339838031005668786736060000000000000)
      constant := (4414257081202553954454452521645570697390243631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree037.table
  base := (-9161769572301231871486672260760207223623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-687608623660339582650546935400000000000000)
      constant := (7502496207941161730215321613959474404962179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/100000000000000000000)
  centralHi := (149071198499985979761/50000000000000000000)
  directionLo := (151127450097060481611/50000000000000000000)
  directionHi := (302254900194120963223/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree038.table
  base := (-372100695552931673230511040234598671671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-832527160108998139593783356055480000000000000)
      constant := (9278881342204866759599989882752000599024737225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree038.table
  base := (-4652411561187937764609694529107146448989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-352198587871020509787456378900000000000000)
      constant := (3942651019850459370481805198714107045877297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151127450097060481611/50000000000000000000)
  centralHi := (302254900194120963223/100000000000000000000)
  directionLo := (61262438898178763413/20000000000000000000)
  directionHi := (153156097245446908533/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree039.table
  base := (-9423994167335250471264714151113781929147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-852361155538320217176229138638840000000000000)
      constant := (9740921907116309554588022693184043313208200973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree039.table
  base := (-2356491765622871782397181837424875708171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (24)
      square := (419713802042535923109145560000000000000)
      linear := (-20032936883992846013868849450000000000000)
      constant := (229945177897452573271506860237725372875487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61262438898178763413/20000000000000000000)
  centralHi := (153156097245446908533/50000000000000000000)
  directionLo := (19394777838567973847/6250000000000000000)
  directionHi := (310316445417087581553/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree040.table
  base := (-1190485669334708090870060992318928605243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-109024393870955286844834365152775000000000000)
      constant := (1276827966985574930012001305520109208559409037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree040.table
  base := (-1190696543467638669695010284941320381791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-92246784988180486677955550325000000000000)
      constant := (1085082410746971408519145707306584349691643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19394777838567973847/6250000000000000000)
  centralHi := (310316445417087581553/100000000000000000000)
  directionLo := (314269680527354455289/100000000000000000000)
  directionHi := (31426968052735445529/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree041.table
  base := (-4801253245201556448239493564589874748507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-446014573198482186170560351902780000000000000)
      constant := (5349988359153466127428792439425115823183087213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree041.table
  base := (-4801974055697151279304893354711181678799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-377381415993572665174005112500000000000000)
      constant := (4546596169052538251386252739922798094672427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/100000000000000000000)
  centralHi := (31426968052735445529/10000000000000000000)
  directionLo := (318173801406141181209/100000000000000000000)
  directionHi := (31817380140614118121/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree042.table
  base := (-9660120763131736199616764919774886009841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-911863141826286449923566486388920000000000000)
      constant := (11196972421556730054049244636274212877358684519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree042.table
  base := (-9661351968485064380109670800099232672547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-85727931563205196363597338600000000000000)
      constant := (1057290956121143378350358557599702301982359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318173801406141181209/100000000000000000000)
  centralHi := (31817380140614118121/10000000000000000000)
  directionLo := (161015297179882650819/50000000000000000000)
  directionHi := (322030594359765301639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree043.table
  base := (-9696947696654598143930913788531764296483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-931697137255608527506012268972280000000000000)
      constant := (11705603811872203371825352916338973740176388197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree043.table
  base := (-4848999301063317563985367883185991776051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-394169968075274102098370934900000000000000)
      constant := (4973966145243677743517866620653978222046623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161015297179882650819/50000000000000000000)
  centralHi := (322030594359765301639/100000000000000000000)
  directionLo := (81460434992306556361/25000000000000000000)
  directionHi := (65168347993845245089/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree044.table
  base := (-9713170394816188586452325043508262206207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-951531132684930605088458051555640000000000000)
      constant := (12225865022423070908676782930643031770650921513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree044.table
  base := (-1942813383753393542106863540985640261291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-805128488232249641121107692200000000000000)
      constant := (10390128563822177019894808073966938564725715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81460434992306556361/25000000000000000000)
  centralHi := (65168347993845245089/20000000000000000000)
  directionLo := (329608821648696131053/100000000000000000000)
  directionHi := (164804410824348065527/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree045.table
  base := (-2427235396076830780293568419427310824381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-242841282028563170667725958534750000000000000)
      constant := (3189437789923358060539099038783879533876008379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree045.table
  base := (-1941941202179195435215544001639577995201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-30441371863479669557239759800000000000000)
      constant := (401563088873982492497294974991802110023995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329608821648696131053/100000000000000000000)
  centralHi := (164804410824348065527/50000000000000000000)
  directionLo := (333333333333333333333/100000000000000000000)
  directionHi := (166666666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree046.table
  base := (-302637145463199357557831797956459131777/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-123899890442946845031668702090295000000000000)
      constant := (1662657267748761227072328153831718371834932572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree046.table
  base := (-4842520062981823700621368099575133763081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-419352796197826257484919668500000000000000)
      constant := (5652076721566128377481436784311471388396813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333333333333333333333/100000000000000000000)
  centralHi := (166666666666666666667/50000000000000000000)
  directionLo := (1316471431258949749/390625000000000000)
  directionHi := (67403337280458227149/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree047.table
  base := (-481980893147046233992590960678580579203/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-252758279743224209458948849826430000000000000)
      constant := (3464095641186494430371807291262817998308783385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree047.table
  base := (-9640172807141446506933324094078018995649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-855494144477353951894205159400000000000000)
      constant := (11775975898760735753238128944459893487117477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1316471431258949749/390625000000000000)
  centralHi := (67403337280458227149/20000000000000000000)
  directionLo := (170330107963954351739/50000000000000000000)
  directionHi := (340660215927908703479/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree048.table
  base := (-478735891924546613375117409150792049541/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-257716778600554728854560295472270000000000000)
      constant := (3605780397043194465034274908022677359703284095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree048.table
  base := (-9575190343954006582040547096780097167087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-96920299617672820979841220200000000000000)
      constant := (1361963159629533247316963526709659708498739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170330107963954351739/50000000000000000000)
  centralHi := (340660215927908703479/100000000000000000000)
  directionLo := (344265186329548167571/100000000000000000000)
  directionHi := (86066296582387041893/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree049.table
  base := (-9489762509127859175131005699545831360749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1050701109831540993000686964472440000000000000)
      constant := (15001472843554481735741931510709132017370241291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree049.table
  base := (-9490164647803451159095003067971741187443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-889071248640756825742936804200000000000000)
      constant := (12749229115239589837428175814164762987939039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344265186329548167571/100000000000000000000)
  centralHi := (86066296582387041893/25000000000000000000)
  directionLo := (86958199124991821527/25000000000000000000)
  directionHi := (347832796499967286109/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree050.table
  base := (-4692406769830468316827283733000359801023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-535267552630431535291566373527900000000000000)
      constant := (7795717177544468385215960195305935471615422057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree050.table
  base := (-2346288912059569828404157752402130647583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-226464950180614565666825656650000000000000)
      constant := (3312664079096074528231400703185142472515259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86958199124991821527/25000000000000000000)
  centralHi := (347832796499967286109/100000000000000000000)
  directionLo := (35136418446315325911/10000000000000000000)
  directionHi := (351364184463153259111/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree051.table
  base := (-4629961183320647420273499983368413173529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-545184550345092574082789264819580000000000000)
      constant := (8096502237348804100774901455836832673506957311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree051.table
  base := (-926021328984332117393698329218344997801/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-51258241822453316643981580500000000000000)
      constant := (764552705088674091048888934561724825032985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/10000000000000000000)
  centralHi := (351364184463153259111/100000000000000000000)
  directionLo := (354860431614918044423/100000000000000000000)
  directionHi := (44357553951864755553/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree052.table
  base := (-1823026379073467477119350255432714938201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1110203096119507225748024312222520000000000000)
      constant := (16806181827651829879675167409110321903325508795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree052.table
  base := (-364615167852578137959558550870030271439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-939436904885861136516034271400000000000000)
      constant := (14283105117035307744150181438162729566778675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354860431614918044423/100000000000000000000)
  centralHi := (44357553951864755553/12500000000000000000)
  directionLo := (22395160411940415701/6250000000000000000)
  directionHi := (358322566591046651217/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree053.table
  base := (-8950477915320163316612416505701791077077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1130037091548829303330470094805880000000000000)
      constant := (17430965267220837910217178687052928912099375843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree053.table
  base := (-4475344028593872573921853168443111318841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-478112728483781286720200046900000000000000)
      constant := (7407062328042173282745612022952035994391293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/6250000000000000000)
  centralHi := (358322566591046651217/100000000000000000000)
  directionLo := (45218946100276962187/12500000000000000000)
  directionHi := (361751568802215697497/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree054.table
  base := (-876599028074802465553884110052656741893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-574935543489075690456457938694620000000000000)
      constant := (9033676918422332025070350976248254126665031935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree054.table
  base := (-4383084391723846335781041061544706360277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-18018777945356740932680850300000000000000)
      constant := (284351972743456827779157131938455293639723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45218946100276962187/12500000000000000000)
  centralHi := (361751568802215697497/100000000000000000000)
  directionLo := (11410886614690960697/3125000000000000000)
  directionHi := (73029674334022148461/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree055.table
  base := (-2140423473841761969641777491884504671157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-292426270601868364623840414993150000000000000)
      constant := (4678836684645834972755524663492778585831458563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree055.table
  base := (-8561845470535032672520623520993224076631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-989802561130965447289131738600000000000000)
      constant := (15905750082645374258285798299933182949930963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11410886614690960697/3125000000000000000)
  centralHi := (73029674334022148461/20000000000000000000)
  directionLo := (368513865595044427679/100000000000000000000)
  directionHi := (2303211659969027673/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree056.table
  base := (-4168804766839939937044229855102549648619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-594769538918397768038903721277980000000000000)
      constant := (9687471653400513061955212589732499206708598621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree056.table
  base := (-8337738200854484162639633572530282866297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1006591113212666884213497561000000000000000)
      constant := (16466354777355535826803315389541682362609981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368513865595044427679/100000000000000000000)
  centralHi := (2303211659969027673/625000000000000000)
  directionLo := (11620278146306604833/3125000000000000000)
  directionHi := (371848900681811354657/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree057.table
  base := (-50585965787632094402461132608794965597/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-151171634158264701707531653142415000000000000)
      constant := (2505767873277058920852427386750947010146130460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree057.table
  base := (-8093863712532662773347987225086587455903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-113708851699374257904207042600000000000000)
      constant := (1892980017816414975953161863324740237632291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/3125000000000000000)
  centralHi := (371848900681811354657/100000000000000000000)
  directionLo := (46894286155928144953/12500000000000000000)
  directionHi := (3001234313979401277/800000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree058.table
  base := (-978767916242565342130670549723904855777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-153650883586929961405337375965335000000000000)
      constant := (2591118164199415673538902133329486364516049143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree058.table
  base := (-783023595671799168551493183599962393419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-520084108688034879031114602900000000000000)
      constant := (8808572927470481851363876381214005076888435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46894286155928144953/12500000000000000000)
  centralHi := (3001234313979401277/800000000000000000)
  directionLo := (378430808131697803691/100000000000000000000)
  directionHi := (94607702032924450923/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree059.table
  base := (-3773394003391427837752307520501493582347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-624520532062380884412572395153020000000000000)
      constant := (10711674951240019519073006097221951644128019773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree059.table
  base := (-377343328099954515117977164003832686901/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-264239192364442798746648757050000000000000)
      constant := (4551832886790832465091072079609482587268365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378430808131697803691/100000000000000000000)
  centralHi := (94607702032924450923/25000000000000000000)
  directionLo := (76335840165856303319/20000000000000000000)
  directionHi := (95419800207320379149/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree060.table
  base := (-1810924654798739111243117452668670625337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-317218764888520961601897643222350000000000000)
      constant := (5532339107613336368948460316448043124493577183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree060.table
  base := (-7243765221422007097033295046364133675817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-119305035726608070212328983400000000000000)
      constant := (2089708552811398883079219294860907598972549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76335840165856303319/20000000000000000000)
  centralHi := (95419800207320379149/25000000000000000000)
  directionLo := (48112522432468813709/12500000000000000000)
  directionHi := (384900179459750509673/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree061.table
  base := (-6920883562679492771383618762703864808591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1288709054983405923990036355472760000000000000)
      constant := (22846964628514943724648030876599685467667935769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree061.table
  base := (-6920940015006572062853405761898022023343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1090533873621174068835326673000000000000000)
      constant := (19417281921198208554954243865428753405369739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/12500000000000000000)
  centralHi := (384900179459750509673/100000000000000000000)
  directionLo := (388094426590510681029/100000000000000000000)
  directionHi := (38809442659051068103/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree062.table
  base := (-3289174921069425315628779711554410074289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-654271525206364000786241069028060000000000000)
      constant := (11788087136110378217817459903317645146809706151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree062.table
  base := (-6578397678512072496744184437097335858403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1107322425702875505759692495400000000000000)
      constant := (20037046202984684925071142610198371931823119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388094426590510681029/100000000000000000000)
  centralHi := (38809442659051068103/10000000000000000000)
  directionLo := (195631298462877879397/50000000000000000000)
  directionHi := (78252519385151151759/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree063.table
  base := (-777012912817053817755460179388579991109/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-166047130730256259894365990079935000000000000)
      constant := (3039623146786538911596864020292575508504876531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree063.table
  base := (-1554035956852683293261037378615523592737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (8)
      square := (139904600680845307703048520000000000000)
      linear := (-10408434979486823543370910350000000000000)
      constant := (191358052491150638788486387871384476407263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195631298462877879397/50000000000000000000)
  centralHi := (78252519385151151759/20000000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree064.table
  base := (-583414882128830205529511675212522179383/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-674105520635686078368686851611420000000000000)
      constant := (12534698589226160005783347021398017884251946485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree064.table
  base := (-5834183143534383087920992199759077851953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1140899529866278379608424140200000000000000)
      constant := (21306152192967501364313878042606504897997269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198761597999981306347/50000000000000000000)
  directionHi := (79504639199992522539/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree065.table
  base := (-339530654295936498450136207092328283767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-171005629587586779289977435725775000000000000)
      constant := (3229176269285375253625650449883984418919643106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree065.table
  base := (-217300781224617794732448404358612281249/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1157688081947979816532789962600000000000000)
      constant := (21955493669353606639615901632057936710156925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/50000000000000000000)
  centralHi := (79504639199992522539/20000000000000000000)
  directionLo := (80123361676977539847/20000000000000000000)
  directionHi := (100154202096221924809/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree066.table
  base := (-2505565820994770006998999774282576335401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-693939516065008155951132634194780000000000000)
      constant := (13304511996468728835343389549539851971637416559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree066.table
  base := (-2505578121953256914136523109657794367277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-65248701890537847414286432500000000000000)
      constant := (1256371889461709152310168227671026616898169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80123361676977539847/20000000000000000000)
  centralHi := (100154202096221924809/25000000000000000000)
  directionLo := (403686713879665555389/100000000000000000000)
  directionHi := (40368671387966555539/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree067.table
  base := (-1142518794144853900396060292943831364613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-351928256889834597371177762743230000000000000)
      constant := (6849059650890638014397985333936716699246434867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree067.table
  base := (-4570095998198738366855376361494538950609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1191265186111382690381521607400000000000000)
      constant := (23283753142539614663440937793239647448333557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403686713879665555389/100000000000000000000)
  centralHi := (40368671387966555539/10000000000000000000)
  directionLo := (81346689856547229703/20000000000000000000)
  directionHi := (101683362320684037129/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree068.table
  base := (-513665429945810708854694547964595437111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-178443377873582558383394604194535000000000000)
      constant := (3524381738789406956874548686989206397599526449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree068.table
  base := (-410934105783916933535601597263773260613/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-604026869096542063652943714900000000000000)
      constant := (11981335502451393016102294850369390609817245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81346689856547229703/20000000000000000000)
  centralHi := (101683362320684037129/25000000000000000000)
  directionLo := (102439382858809859/25000000000000000)
  directionHi := (409757531435239436001/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree069.table
  base := (-907219601804610608291400368921748941583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-361845254604495636162400654034910000000000000)
      constant := (7251367462468493834188602716087648242162739097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree069.table
  base := (-3628893311747211019893274814327810970361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-136093587808309507136694805800000000000000)
      constant := (2739049727377717214683198828557016567088917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/25000000000000000)
  centralHi := (409757531435239436001/100000000000000000000)
  directionLo := (41275945824459355491/10000000000000000000)
  directionHi := (412759458244593554911/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree070.table
  base := (-3128741729794747606847054879764544010149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1467215013847304622232048398723000000000000000)
      constant := (29827486369362747689950638305415464245370815891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree070.table
  base := (-3128754335930278733056788951273219018599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1241630842356487001154619074600000000000000)
      constant := (25350082724477421149833616888315623086497827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41275945824459355491/10000000000000000000)
  centralHi := (412759458244593554911/100000000000000000000)
  directionLo := (207869854820774521421/50000000000000000000)
  directionHi := (415739709641549042843/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree071.table
  base := (-326114348198134320509303341268399583017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-185881126159578337476811772663295000000000000)
      constant := (3832637928077474161258331450237304208960552303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree071.table
  base := (-652231361395519895865990172361751779001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-314604848609547109519746224250000000000000)
      constant := (6514644125906613648331600533096232701966973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207869854820774521421/50000000000000000000)
  centralHi := (415739709641549042843/100000000000000000000)
  directionLo := (52337343559491033179/12500000000000000000)
  directionHi := (418698748475928265433/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree072.table
  base := (-129337420373964645402756154924479818181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-188360375588243597174617495486215000000000000)
      constant := (3938290122344162078744935136962169484291325158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree072.table
  base := (-129337983656230858333813834371649753777/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (5)
      previous := (0)
      next := (4)
      square := (69952300340422653851524260000000000000)
      linear := (-5903740493147638310200697775000000000000)
      constant := (123967263213916824528921467331256700492446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52337343559491033179/12500000000000000000)
  centralHi := (418698748475928265433/100000000000000000000)
  directionLo := (421637021355783910933/100000000000000000000)
  directionHi := (210818510677891955467/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree073.table
  base := (-1510194513085306416550364691803899970513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1526717000135270854979385746473080000000000000)
      constant := (32363139000936756450245682994619631241044792967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree073.table
  base := (-1510202131266268333586456613610537386599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1291996498601591311927716541800000000000000)
      constant := (27505139751468414691521262208432515490561827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421637021355783910933/100000000000000000000)
  centralHi := (210818510677891955467/50000000000000000000)
  directionLo := (16982198377371377937/4000000000000000000)
  directionHi := (212277479717142224213/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree074.table
  base := (-931302951048315192526440328426257666073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1546550995564592932561831529056440000000000000)
      constant := (33231557465404158308866310958156174278121355007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree074.table
  base := (-232827347351249876758169629258839596279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-327196262670823187213020591050000000000000)
      constant := (7060802293686117519458150700510011330900467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16982198377371377937/4000000000000000000)
  centralHi := (212277479717142224213/50000000000000000000)
  directionLo := (106863244787063026399/25000000000000000000)
  directionHi := (427452979148252105597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree075.table
  base := (-166362356125579401547292816057745541851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-783192495496957505072138655819900000000000000)
      constant := (17055788175305908169219077522923193775093552109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree075.table
  base := (-66546030501826211149706322567167851367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-147285955862777131752938687400000000000000)
      constant := (3221237456307242519391688880161492482229495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106863244787063026399/25000000000000000000)
  centralHi := (427452979148252105597/100000000000000000000)
  directionLo := (53791435363991901183/12500000000000000000)
  directionHi := (86066296582387041893/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree076.table
  base := (285539640886182789130618361117888639527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1586218986423237087726723094223160000000000000)
      constant := (35003195638539231960979081466715458269899084607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree076.table
  base := (142767522407378233823324037902830929699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-671181077423347811350407004500000000000000)
      constant := (14874461766548087403339165747023376435101873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53791435363991901183/12500000000000000000)
  centralHi := (86066296582387041893/20000000000000000000)
  directionLo := (108297714942321821187/25000000000000000000)
  directionHi := (433190859769287284749/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree077.table
  base := (230872409425282236952912755422523783653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-401513245463139791327292219201630000000000000)
      constant := (8976603828526476357580049930567723084552025773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree077.table
  base := (923485755492438100598126408506006672277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1359150706928397059625179831400000000000000)
      constant := (30516568441666442400303019698029662180151479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/25000000000000000000)
  centralHi := (433190859769287284749/100000000000000000000)
  directionLo := (4360314860077462993/1000000000000000000)
  directionHi := (436031486007746299301/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree078.table
  base := (1581124884105672099347433334003165384053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1625886977281881242891614659389880000000000000)
      constant := (36821235364684862895795757639773915422070442173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree078.table
  base := (49410050169852421278426045311405229281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3750000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (12)
      square := (209856901021267961554572780000000000000)
      linear := (-19110267486251368007632578525000000000000)
      constant := (434639886421883226022499517293736862751372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4360314860077462993/1000000000000000000)
  centralHi := (436031486007746299301/100000000000000000000)
  directionLo := (10971343143406388343/2500000000000000000)
  directionHi := (438853725736255533721/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree079.table
  base := (2258445049921265506717831967921239635701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1645720972711203320474060441973240000000000000)
      constant := (37747655779696853541404893127193644439167495741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree079.table
  base := (2258442281416465725289976851435095251617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1392727811091799933473911476200000000000000)
      constant := (32081433666766500586780305941988747571793659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10971343143406388343/2500000000000000000)
  centralHi := (438853725736255533721/100000000000000000000)
  directionLo := (220828965715019894667/50000000000000000000)
  directionHi := (88331586286007957867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree080.table
  base := (2955449858313735501419829804703723862407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1665554968140525398056506224556600000000000000)
      constant := (38685676550271833608635101013028512016275382687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree080.table
  base := (2955447520966486091813511776692529834877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1409516363173501370398277298600000000000000)
      constant := (32878653967752490387752049377970698305541679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220828965715019894667/50000000000000000000)
  centralHi := (88331586286007957867/20000000000000000000)
  directionLo := (111111111111111111111/25000000000000000000)
  directionHi := (88888888888888888889/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree081.table
  base := (183606953848991556108895290553981634067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-421347240892461868909738001784990000000000000)
      constant := (9908824417241643658359038081962870627685703735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree081.table
  base := (1836068551975659878646168645016358955479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-26413053986207459394863761500000000000000)
      constant := (623809865173887836450168930145016358955479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/25000000000000000000)
  centralHi := (88888888888888888889/20000000000000000000)
  directionLo := (447213595499957939281/100000000000000000000)
  directionHi := (223606797749978969641/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree082.table
  base := (1102128127698706925330793148024065968111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-426305739749792388305349447430830000000000000)
      constant := (10149129782382271328182817062660219097684244551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree082.table
  base := (4408510845552987414576468911507557123163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1443093467336904244247008943400000000000000)
      constant := (34502669916688773487158474910610704042325401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447213595499957939281/100000000000000000000)
  centralHi := (223606797749978969641/50000000000000000000)
  directionLo := (112491426285092149629/25000000000000000000)
  directionHi := (449965705140368598517/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree083.table
  base := (2582284997839406778246111326951588132163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-862528477214245815401921786153340000000000000)
      constant := (20784670463351040598152921420943115835342634683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree083.table
  base := (5164568590418754104333079194142735821749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1459882019418605681171374765800000000000000)
      constant := (35329465555454457500398121085241853867187223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112491426285092149629/25000000000000000000)
  centralHi := (449965705140368598517/100000000000000000000)
  directionLo := (452701084165852502771/100000000000000000000)
  directionHi := (113175271041463125693/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree084.table
  base := (594031139347950196881399817301747709223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-872445474928906854193144677445020000000000000)
      constant := (21276881528029512432700264268932666491756070715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree084.table
  base := (5940310207784268549009361466866611145727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-164074507944478568677304509800000000000000)
      constant := (4018457736906261969281570552400599833437181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452701084165852502771/100000000000000000000)
  centralHi := (113175271041463125693/25000000000000000000)
  directionLo := (56927504255331102129/12500000000000000000)
  directionHi := (455420034042648817033/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree085.table
  base := (1347147317540590278232924290211270710257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1764724945287135785968735137473400000000000000)
      constant := (43549785513867333938903929173244296624136722685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree085.table
  base := (1683933896852090355437956380800614082749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-373364780895502138755026602650000000000000)
      constant := (9253158035954490646185368083531616580234223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/12500000000000000000)
  centralHi := (455420034042648817033/100000000000000000000)
  directionLo := (229061423645425586101/50000000000000000000)
  directionHi := (458122847290851172203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree086.table
  base := (7550845479951552425813466136485452895401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1784558940716457863551180920056760000000000000)
      constant := (44557408296974250614103357749093610396221543441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree086.table
  base := (1510168927236854252510873180880105370437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1510247675663709991944472233000000000000000)
      constant := (37869003087925389524599968325418814225008995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229061423645425586101/50000000000000000000)
  centralHi := (458122847290851172203/100000000000000000000)
  directionLo := (92161961570345426109/20000000000000000000)
  directionHi := (230404903925863565273/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree087.table
  base := (2096409496737993484865186225597397942271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-451098234036444985283406675660030000000000000)
      constant := (11394157850677903522039188944917896227468305111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree087.table
  base := (8385637275314603646166755575746571807809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-169670691971712380985426450600000000000000)
      constant := (4303914718039012099291985201727239715423427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92161961570345426109/20000000000000000000)
  centralHi := (230404903925863565273/50000000000000000000)
  directionLo := (463481191435871337899/100000000000000000000)
  directionHi := (4634811914358713379/1000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree088.table
  base := (462005701903761146478192959264606241931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-456056732893775504679018121305870000000000000)
      constant := (11651863707204100199067413966101466242988555855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree088.table
  base := (924011343795610995669797672389360965743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-771912389913556432896601938900000000000000)
      constant := (19805660132645176489598055161772563730375305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463481191435871337899/100000000000000000000)
  centralHi := (4634811914358713379/1000000000000000000)
  directionLo := (466137265853400687551/100000000000000000000)
  directionHi := (7283394778959385743/1562500000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree089.table
  base := (1264284196658400726272766348107706579977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-230507615875553012037314783475855000000000000)
      constant := (5956234821670552190731866591634954026529043057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree089.table
  base := (10114273067256022767477978755215316117251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1560613331908814302717569700200000000000000)
      constant := (40497266495208097060784607483390813535165777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137265853400687551/100000000000000000000)
  centralHi := (7283394778959385743/1562500000000000000)
  directionLo := (234389145663655405553/50000000000000000000)
  directionHi := (468778291327310811107/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree090.table
  base := (11008116541321718450544132400048746917267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1863894922433746173880964050390200000000000000)
      constant := (48703902634714966290358539083539961899976151947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree090.table
  base := (1376014514339340881896436685317615261553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (5)
      previous := (0)
      next := (4)
      square := (69952300340422653851524260000000000000)
      linear := (-7302786499956091387231182975000000000000)
      constant := (191634588661087275614644935435317615261553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389145663655405553/50000000000000000000)
  centralHi := (468778291327310811107/100000000000000000000)
  directionLo := (471404520791031682933/100000000000000000000)
  directionHi := (235702260395515841467/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree091.table
  base := (11921642898439085474157755802895926687567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1883728917863068251463409832973560000000000000)
      constant := (49769527011464661691042291276054868386996334247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree091.table
  base := (1490205317352551879631140298987198364563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-199273804509027147070787668125000000000000)
      constant := (5287341778866224698124814034447654355843201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471404520791031682933/100000000000000000000)
  centralHi := (235702260395515841467/50000000000000000000)
  directionLo := (474016200171145372241/100000000000000000000)
  directionHi := (237008100085572686121/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree092.table
  base := (12854852607023088757623629523739288135897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1903562913292390329045855615556920000000000000)
      constant := (50846751702408883303014350049364850531162275777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree092.table
  base := (6427426151955214796815322322144405534359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-805489494076959306745333583700000000000000)
      constant := (21607127867325021737632130092697898949427693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474016200171145372241/100000000000000000000)
  centralHi := (237008100085572686121/50000000000000000000)
  directionLo := (238306784328080184551/50000000000000000000)
  directionHi := (476613568656160369103/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree093.table
  base := (13807745634676681655218441804314557592039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1923396908721712406628301398140280000000000000)
      constant := (51935576706509597354699094771423362739806521599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree093.table
  base := (13807745379221548927493076365929349351881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-180863060026180005601670332200000000000000)
      constant := (4904403962347220246114458802097788048055643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/50000000000000000000)
  centralHi := (476613568656160369103/100000000000000000000)
  directionLo := (23959842947608694083/5000000000000000000)
  directionHi := (479196858952173881661/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree094.table
  base := (739016097668176926530025272498783816653/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-485807726037758621052686795180910000000000000)
      constant := (13259000505717122984095625360706687661346893865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree094.table
  base := (2956064347619550979324976096595110903187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1644556092317321487339398812200000000000000)
      constant := (45074874009634901314461807875040339971930245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23959842947608694083/5000000000000000000)
  centralHi := (479196858952173881661/100000000000000000000)
  directionLo := (120441574381548885661/25000000000000000000)
  directionHi := (96353259505239108529/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree095.table
  base := (3943145384676988746716509482124016200657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-490766224895089140448298240826750000000000000)
      constant := (13537006912676136275870843991864985603085250937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree095.table
  base := (1971572669666158624932211457641042832073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-207668080549877865532970579325000000000000)
      constant := (5752496347444142094252118786231308156465971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120441574381548885661/25000000000000000000)
  centralHi := (96353259505239108529/20000000000000000000)
  directionLo := (96864420967570523383/20000000000000000000)
  directionHi := (121080526209463154229/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree096.table
  base := (16784524369410173149491545310949692983383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-1982898895009678639375638745890360000000000000)
      constant := (55271653589335291313944111076346219112880574703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree096.table
  base := (16784524216601007987957036504861906647941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-186459244053413817909792273000000000000000)
      constant := (5219436218925686809555402853514585719943823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96864420967570523383/20000000000000000000)
  centralHi := (121080526209463154229/25000000000000000000)
  directionLo := (243432247780073828203/50000000000000000000)
  directionHi := (486864495560147656407/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree097.table
  base := (17816150426758008939533498594457171164827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2002732890439000716958084528473720000000000000)
      constant := (56406879838161173477691277156704322221292221907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree097.table
  base := (17816150298032251135366210064333481062333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1694921748562425798112496279400000000000000)
      constant := (47939739581486255450784403016737003988682991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/50000000000000000000)
  centralHi := (486864495560147656407/100000000000000000000)
  directionLo := (244696839394947116693/50000000000000000000)
  directionHi := (489393678789894233387/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree098.table
  base := (4716864923554707494198725389205967152189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-505641721467080698635132577764270000000000000)
      constant := (14388426599163117380157745563144728393523287749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree098.table
  base := (18867459585792344611229473739317934374189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1711710300644127235036862101800000000000000)
      constant := (48914411612590931594951977352961584228103103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244696839394947116693/50000000000000000000)
  centralHi := (489393678789894233387/100000000000000000000)
  directionLo := (98381971649682912551/20000000000000000000)
  directionHi := (122977464562103640689/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree099.table
  base := (19938452157098578250887560095527352007341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2042400881297644872122976093640440000000000000)
      constant := (58712133264338367130052378236731071885667212981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree099.table
  base := (4984613016444949080449150906597740145627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (8)
      square := (139904600680845307703048520000000000000)
      linear := (-16004619006720635851492851150000000000000)
      constant := (462027241326522865110834191156597740145627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98381971649682912551/20000000000000000000)
  centralHi := (122977464562103640689/25000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree100.table
  base := (4205825560451347660033727071783957667163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2062234876726966949705421876223800000000000000)
      constant := (59882160440797831050048966909515148938067848415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree100.table
  base := (5257281931338555302877006842718456939549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-436321851201882527221398436650000000000000)
      constant := (12723332733291394641334660109753398337367823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (124225998749988316467/25000000000000000000)
  directionHi := (496903994999953265869/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree101.table
  base := (691858956808374755181601617722259613847/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-260258609019536128410983457350895000000000000)
      constant := (7632973490706495783487747043809490681149086908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree101.table
  base := (11069743276556176300639788927884629664259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-881037978444615772904979784500000000000000)
      constant := (25948789110993185397361174111552885000934993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/25000000000000000000)
  centralHi := (496903994999953265869/100000000000000000000)
  directionLo := (249691167269380354051/50000000000000000000)
  directionHi := (499382334538760708103/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree102.table
  base := (23269528593222837579324924609362609514023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2101902867585611104870313441390520000000000000)
      constant := (62257015718557629621426702938996507371438810943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree102.table
  base := (23269528538700798170127366157447486302839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-197651612107881442526036154600000000000000)
      constant := (5879075992160811614161627888472342458908517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249691167269380354051/50000000000000000000)
  centralHi := (499382334538760708103/100000000000000000000)
  directionLo := (501848435139387329993/100000000000000000000)
  directionHi := (250924217569693664997/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree103.table
  base := (24419253718560726357216990040206657389759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2121736863014933182452759223973880000000000000)
      constant := (63461843819202083386275858232804381509425268119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree103.table
  base := (12209626836329719212561896742229945497943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-897826530526317209829345606900000000000000)
      constant := (26967824027646478268613251795540208528444461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501848435139387329993/100000000000000000000)
  centralHi := (250924217569693664997/50000000000000000000)
  directionLo := (20172099054062608391/4000000000000000000)
  directionHi := (31518904771972825611/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree104.table
  base := (25588661984930348070931506350092395112923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2141570858444255260035205006557240000000000000)
      constant := (64678272227298518625008081303583790431813165843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree104.table
  base := (25588661946290381581335119936985621766963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1812441613134335856583057036200000000000000)
      constant := (54969470599288483745844695030298611787708001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20172099054062608391/4000000000000000000)
  centralHi := (31518904771972825611/6250000000000000000)
  directionLo := (506744633377394657393/100000000000000000000)
  directionHi := (253372316688697328697/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree105.table
  base := (13388876692036287488704065217686377712279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1080702426936788668808825394570300000000000000)
      constant := (32953150471291152312803987848975389228279131439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree105.table
  base := (13388876675774117773498461139601344711631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-101623898067557627417079047700000000000000)
      constant := (3111841753400925587046199215918804034134893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506744633377394657393/100000000000000000000)
  centralHi := (253372316688697328697/50000000000000000000)
  directionLo := (509175077217315556287/100000000000000000000)
  directionHi := (7955860581520555567/1562500000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree106.table
  base := (27986527908322327331525058149415996094661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2181238849302899415200096571723960000000000000)
      constant := (67145929964807844567962093689243117930869033101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree106.table
  base := (27986527880948163395308401623638389961553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1846018717297738730431788681000000000000000)
      constant := (57066690940875396403163554589838236528961931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509175077217315556287/100000000000000000000)
  centralHi := (7955860581520555567/1562500000000000000)
  directionLo := (102318794961967450853/20000000000000000000)
  directionHi := (255796987404918627133/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree107.table
  base := (14607492775263119037411434207791550864073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1100536422366110746391271177153660000000000000)
      constant := (34198579646872968709075168483372109081235762993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree107.table
  base := (29214985527488776815814654618765985046333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1862807269379440167356154503400000000000000)
      constant := (58130088738075653770458318749706681596250991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102318794961967450853/20000000000000000000)
  centralHi := (255796987404918627133/50000000000000000000)
  directionLo := (20560059566614004569/4000000000000000000)
  directionHi := (257000744582675057113/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree108.table
  base := (7615781575993378238899866238048181797497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-555226710040385892591247034222670000000000000)
      constant := (17414997232295390654388479665873181792973601377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree108.table
  base := (15231563142293706084761475878867727735887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-34807330027058177857046672700000000000000)
      constant := (1096358239863698162045612493878867727735887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20560059566614004569/4000000000000000000)
  centralHi := (257000744582675057113/50000000000000000000)
  directionLo := (516397779494322251357/100000000000000000000)
  directionHi := (258198889747161125679/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree109.table
  base := (1269238006493512537636611655051970301649/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2240740835590865647947433919474040000000000000)
      constant := (70934418870912017953238922453422684510878390225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree109.table
  base := (15865475073012871125552530125156097714083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-948192186771421520602443074100000000000000)
      constant := (30143229792199821254316980031879214638280241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516397779494322251357/100000000000000000000)
  centralHi := (258198889747161125679/50000000000000000000)
  directionLo := (518783001330166756331/100000000000000000000)
  directionHi := (129695750332541689083/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree110.table
  base := (33018457119628349558316221245289852598359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2260574831020187725529879702057400000000000000)
      constant := (72220449118745352523697945671186332167104020719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree110.table
  base := (33018457105904017295833870406597787839073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1913172925624544478129251970600000000000000)
      constant := (61379432633196185801323342970978140271654971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518783001330166756331/100000000000000000000)
  centralHi := (129695750332541689083/25000000000000000000)
  directionLo := (104231461329409545657/20000000000000000000)
  directionHi := (260578653323523864143/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree111.table
  base := (17162823585074334960342670035708195704977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1140204413224754901556162742320380000000000000)
      constant := (36759039836249523165018187629840866298583168057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree111.table
  base := (1716282357930125624876908700666703754353/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (24)
      square := (419713802042535923109145560000000000000)
      linear := (-53610041047395719862600494250000000000000)
      constant := (1735618447191044390521238910260000556315295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104231461329409545657/20000000000000000000)
  centralHi := (260578653323523864143/50000000000000000000)
  directionLo := (523520843972877620583/100000000000000000000)
  directionHi := (65440105496609702573/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree112.table
  base := (17826260154230943269606658997383546630873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1150121410939415940347385633612060000000000000)
      constant := (37413655265999448022102385740433726217599801793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree112.table
  base := (891313007468724894406104130601714907399/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-243343753723493418997247951925000000000000)
      constant := (7949369247662353626849805087631231512498865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523520843972877620583/100000000000000000000)
  centralHi := (65440105496609702573/12500000000000000000)
  directionLo := (131468439624435912057/25000000000000000000)
  directionHi := (525873758497743648229/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree113.table
  base := (36999076529361280872490083735587198277013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2320076817308153958277217049807480000000000000)
      constant := (76148141697078073197417814240868869419993773533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree113.table
  base := (36999076521191226624868296659787925243951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-1963538581869648788902349437800000000000000)
      constant := (64717502280320768175733606986814273981586677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/25000000000000000000)
  centralHi := (525873758497743648229/100000000000000000000)
  directionLo := (66027024022248404689/12500000000000000000)
  directionHi := (528216192177987237513/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree114.table
  base := (19182657913922705889952241093887338444539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1169955406368738017929831416195420000000000000)
      constant := (38740286583788163307044590759465684211101474099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree114.table
  base := (38365315820973661135505391171001017516993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-220036348216816691758523917800000000000000)
      constant := (7316656555089957317339628871513003052550979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66027024022248404689/12500000000000000000)
  centralHi := (528216192177987237513/100000000000000000000)
  directionLo := (8289816934939806909/1562500000000000000)
  directionHi := (530548283836147642177/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree115.table
  base := (9937809549774247847050663148880525890391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-589936202041699528360527153743550000000000000)
      constant := (19706151235834826393367986590644530930054018031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree115.table
  base := (3975123819331767522606091317210114277407/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-998557843016525831375540541300000000000000)
      constant := (33496087063818174602775523405323365427449945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289816934939806909/1562500000000000000)
  centralHi := (530548283836147642177/100000000000000000000)
  directionLo := (106574033851393767591/20000000000000000000)
  directionHi := (133217542314242209489/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree116.table
  base := (160768920462753578639091116673320569077/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-297447350449515023878069299694695000000000000)
      constant := (10022529628027248008276879911610215659321477024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree116.table
  base := (823136872672094644287276768476512675729/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1006952119057376549837723452500000000000000)
      constant := (34072148837838133866899075116721646056117075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106574033851393767591/20000000000000000000)
  centralHi := (133217542314242209489/25000000000000000000)
  directionLo := (267590990639828788447/50000000000000000000)
  directionHi := (107036396255931515379/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree117.table
  base := (42582132141448941383984813128035836895359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2399412799025442268607000180140920000000000000)
      constant := (81547469410068169754252510784493116249964197719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree117.table
  base := (42582132137362016017168398941717008763071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-75210844081350168022215286200000000000000)
      constant := (2566899245918837237279642013941717008763071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/50000000000000000000)
  centralHi := (107036396255931515379/20000000000000000000)
  directionLo := (67185481235821247103/12500000000000000000)
  directionHi := (21499353995462799073/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree118.table
  base := (2201355185184328624944128941472361916223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-604811698613691086547361490681070000000000000)
      constant := (20731575525187520986654343786503159740788505715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree118.table
  base := (2201355185012506527519893785629375928879/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-511870335569538993381044637450000000000000)
      constant := (17619530004979049632384381956559965750398665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67185481235821247103/12500000000000000000)
  centralHi := (21499353995462799073/4000000000000000000)
  directionLo := (107955180457698837509/20000000000000000000)
  directionHi := (269887951144247093773/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree119.table
  base := (22745879160470907744832601448423092131459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1219540394942043211885945872653820000000000000)
      constant := (42158367548064000579991923441396464294984077819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree119.table
  base := (11372939579513133002998713863972863355759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-516067473589964352612136093050000000000000)
      constant := (17914954703971300105026045106077267310605493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107955180457698837509/20000000000000000000)
  centralHi := (269887951144247093773/50000000000000000000)
  directionLo := (542058263006687465157/100000000000000000000)
  directionHi := (271029131503343732579/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree120.table
  base := (46976095989095489336078513102397217778003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2458914785313408501354337527891000000000000000)
      constant := (85718768396069938715281962062481909254824994123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree120.table
  base := (9395219197333283167538192877364741284269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-231228716271284316374767799400000000000000)
      constant := (8094597336400537261668338453160471119264035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542058263006687465157/100000000000000000000)
  centralHi := (271029131503343732579/50000000000000000000)
  directionLo := (272165526975908677577/50000000000000000000)
  directionHi := (108866210790363471031/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree121.table
  base := (24240058352068425464671927813883994071797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1239374390371365289468391655237180000000000000)
      constant := (43566201000223694196281671919043197054054447677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree121.table
  base := (24240058351047413032255024706260000791747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1048923499261630142148638008500000000000000)
      constant := (37026395827483592761634884327569020021377169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/50000000000000000000)
  centralHi := (108866210790363471031/20000000000000000000)
  directionLo := (109318878899989718491/20000000000000000000)
  directionHi := (68324299312493574057/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree122.table
  base := (50003820462156324578464375750166625816707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2498582776172052656519229093057720000000000000)
      constant := (88557635909135083477112761987433408857793108987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree122.table
  base := (5000382046043979314327063733853676724679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1057317775302480860610820919700000000000000)
      constant := (37632032848933502873520224189070246357831665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109318878899989718491/20000000000000000000)
  centralHi := (68324299312493574057/12500000000000000000)
  directionLo := (274424200782854867323/50000000000000000000)
  directionHi := (548848401565709734647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree123.table
  base := (51547207259339162141339320590950205650033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2518416771601374734101674875641080000000000000)
      constant := (89994470122010795623709166287538355539232707353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree123.table
  base := (3221700453618521136362425506681587064027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3750000000000000000000000000000000000000
      center := (15)
      previous := (0)
      next := (12)
      square := (209856901021267961554572780000000000000)
      linear := (-29603112537314766085361217525000000000000)
      constant := (1062294418836132799947755408415089522384162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274424200782854867323/50000000000000000000)
  centralHi := (548848401565709734647/100000000000000000000)
  directionLo := (110218637934553283737/20000000000000000000)
  directionHi := (275546594836383209343/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree124.table
  base := (26555138545979944168930610096773975258763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1269125383515348405842060329112220000000000000)
      constant := (45721452319477578439451316646761374941266025283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree124.table
  base := (5311027709074720823509304139266735365767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1074106327384182297535186742100000000000000)
      constant := (38858094514935243620674275344801009274378545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218637934553283737/20000000000000000000)
  centralHi := (275546594836383209343/50000000000000000000)
  directionLo := (553328871021721438881/100000000000000000000)
  directionHi := (276664435510860719441/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree125.table
  base := (54693029956377409584560492049088478380431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2558084762460018889266566440807800000000000000)
      constant := (92902939459851502963185214112219843935787389671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree125.table
  base := (13673257488839557367685685855084614885699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-541250301712516507998684826650000000000000)
      constant := (19739259579693914997223961549337284601913873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553328871021721438881/100000000000000000000)
  centralHi := (276664435510860719441/50000000000000000000)
  directionLo := (111111111111111111111/20000000000000000000)
  directionHi := (138888888888888888889/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree126.table
  base := (56295465849030684542435522111471455517329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2577918757889340966849012223391160000000000000)
      constant := (94374574584585734551013958027978536906230738489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree126.table
  base := (28147732924087091781874940399540118736991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-40403514054291990165168613500000000000000)
      constant := (1485328630052242387853802389399540118736991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/20000000000000000000)
  centralHi := (138888888888888888889/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree127.table
  base := (7239698095804358892838740354313711621993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-324719094164832880553932250746815000000000000)
      constant := (11982226251630774227207900100928930634080277713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree127.table
  base := (28958792382857564064061992557446511194801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1099289155506734452921735475700000000000000)
      constant := (40734156070956407831277628266551055802259627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111554670204543406397/20000000000000000000)
  centralHi := (278886675511358515993/50000000000000000000)
  directionLo := (559982363037962336603/100000000000000000000)
  directionHi := (139995590759490584151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree128.table
  base := (29779693352588939346352200538454938446013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1308793374373992561006951894278940000000000000)
      constant := (48676322872561776982624402609519194682748702533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree128.table
  base := (29779693352286547442287179109875101659857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1107683431547585171383918386900000000000000)
      constant := (41369368337979412500352389931966627744816139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559982363037962336603/100000000000000000000)
  centralHi := (139995590759490584151/25000000000000000000)
  directionLo := (562182695141045214577/100000000000000000000)
  directionHi := (281091347570522607289/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree129.table
  base := (61220871661917265219006848929997570634969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2637420744177307199596349571141240000000000000)
      constant := (98859081780710719810500673913297532160715041729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree129.table
  base := (12244174332281822004097295625681506894109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-248017268352985753299133621800000000000000)
      constant := (9335446624985440518401478547385222603411635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562182695141045214577/100000000000000000000)
  centralHi := (281091347570522607289/50000000000000000000)
  directionLo := (564374448853346406099/100000000000000000000)
  directionHi := (5643744488533464061/1000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree130.table
  base := (1258040792667548597114275856861503731537/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1328627369803314638589397676862300000000000000)
      constant := (50188559059851368913037196847085486026554425425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree130.table
  base := (62902039632950490175321611242872448735583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2248943967258573216616568418600000000000000)
      constant := (85309160988554872206546291913557556115860741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564374448853346406099/100000000000000000000)
  centralHi := (5643744488533464061/1000000000000000000)
  directionLo := (28327886186626582389/5000000000000000000)
  directionHi := (566557723732531647781/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree131.table
  base := (64602890616347058147052616898307458446923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2677088735035951354761241136307960000000000000)
      constant := (101906754761996714285492554175035349276097859843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree131.table
  base := (16150722653997093744409601616044252663547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-566433129835068663385233560250000000000000)
      constant := (21652290191732477098368704586383194821915769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28327886186626582389/5000000000000000000)
  centralHi := (566557723732531647781/100000000000000000000)
  directionLo := (7109157717816515249/1250000000000000000)
  directionHi := (568732617425321219921/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree132.table
  base := (4145214037979799054327589181960371984937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-337115341308159179042960864861415000000000000)
      constant := (12930998963436467547202494960541324557538732834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree132.table
  base := (66323424607375463315820379908675577356083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-253613452380219565607255562600000000000000)
      constant := (9768779884434344010709471239726026732068249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7109157717816515249/1250000000000000000)
  centralHi := (568732617425321219921/100000000000000000000)
  directionLo := (570899225718450178671/100000000000000000000)
  directionHi := (35681201607403136167/6250000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree133.table
  base := (13612728320855408921088857390521784738939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2716756725894595509926132701474680000000000000)
      constant := (105000828956088823336935769998935062524101722495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree133.table
  base := (1361272832080478514978556076420157185189/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1149654811751838763694832942900000000000000)
      constant := (44619367783704531960186093850083606100002575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570899225718450178671/100000000000000000000)
  centralHi := (35681201607403136167/6250000000000000000)
  directionLo := (114611528517578904459/20000000000000000000)
  directionHi := (71632205323486815287/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree134.table
  base := (34911770801558042506601352097168315655903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1368295360661958793754289242029020000000000000)
      constant := (53282633253845411393317636275078210001930788023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree134.table
  base := (8727942700362933728533379643872756090551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-289512271948172370539253963525000000000000)
      constant := (11321038823668499246165116208134564414444877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114611528517578904459/20000000000000000000)
  centralHi := (71632205323486815287/12500000000000000000)
  directionLo := (575207960246434869807/100000000000000000000)
  directionHi := (35950497515402179363/6250000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree135.table
  base := (8950390575152265207310465473649124020867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-344553089594154958136378033330175000000000000)
      constant := (13517663045275298952208452178966316582752599547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree135.table
  base := (14320624920207907749426123178043590631413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (40)
      previous := (0)
      next := (32)
      square := (559618402723381230812194080000000000000)
      linear := (-86403212135817792638459167800000000000000)
      constant := (3403990519468354563312976500890217953157065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575207960246434869807/100000000000000000000)
  centralHi := (35950497515402179363/6250000000000000000)
  directionLo := (577350269189625764509/100000000000000000000)
  directionHi := (57735026918962576451/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree136.table
  base := (3670119529783080829094477079364015486911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-694064678045640435668367512306190000000000000)
      constant := (27432235629882480208068934900222632101080576755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree136.table
  base := (73402390595511626784779047939589151491121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2349675279748781838162763353000000000000000)
      constant := (93257035876222947986300528990368907090260267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577350269189625764509/100000000000000000000)
  centralHi := (57735026918962576451/10000000000000000000)
  directionLo := (36217791140014715081/6250000000000000000)
  directionHi := (579484658240235441297/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree137.table
  base := (15044267916715533103382288683357090897257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2796092707611883820255915831808120000000000000)
      constant := (111328180979581487868856433346857342747195057685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree137.table
  base := (75221339583451697560356157590248713733923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2366463831830483275087129175400000000000000)
      constant := (94616186141002681317588303319936715270815921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/6250000000000000000)
  centralHi := (579484658240235441297/100000000000000000000)
  directionLo := (581611214591217803263/100000000000000000000)
  directionHi := (70997462718654517/12207031250000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree138.table
  base := (77059971562148480986065036276406467480807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2815926703041205897838361614391480000000000000)
      constant := (112939019742266807998843621233476259624552537087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree138.table
  base := (77059971562042693245789224032309125108489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-264805820434687190223499444200000000000000)
      constant := (10665021646656523626883969450096927375325467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581611214591217803263/100000000000000000000)
  centralHi := (70997462718654517/12207031250000000)
  directionLo := (583730023847275428749/100000000000000000000)
  directionHi := (466984019077820343/80000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree139.table
  base := (78918286528605960432296164373765873782139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2835760698470527975420807396974840000000000000)
      constant := (114561458807497188448206731055003712361853515699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree139.table
  base := (78918286528517124672782753110060246455593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2400040935993886148935860820200000000000000)
      constant := (97364061912866319751858815840971626654301011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583730023847275428749/100000000000000000000)
  centralHi := (466984019077820343/80000000000000000)
  directionLo := (585841170065069664307/100000000000000000000)
  directionHi := (146460292516267416077/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree140.table
  base := (80796284480230330161937152302675870847391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2855594693899850053003253179558200000000000000)
      constant := (116195498175185484948026956823750037577821255031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree140.table
  base := (40398142240077866882634906202164112641833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1208414744037793792930113321300000000000000)
      constant := (49376393709901041339621884257458431041329491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585841170065069664307/100000000000000000000)
  centralHi := (146460292516267416077/25000000000000000000)
  directionLo := (587944735792131242333/100000000000000000000)
  directionHi := (293972367896065621167/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree141.table
  base := (10336745676793607154153108577253418101017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-359428586166146516323212370267695000000000000)
      constant := (14730142230655757557764658255635311769374685697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree141.table
  base := (82693965414286220983061823197538785333039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-270402004461921002531621385000000000000000)
      constant := (11127930148960427704058387938592616355999117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587944735792131242333/100000000000000000000)
  centralHi := (293972367896065621167/50000000000000000000)
  directionLo := (147510200526130596333/25000000000000000000)
  directionHi := (590040802104522385333/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree142.table
  base := (84611329328334622563953203349483646713707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2895262684758494208168144744724920000000000000)
      constant := (119498377817594745876164692749441525524353885987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree142.table
  base := (10576416166035253939362887324540391256499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 33750000000000000000000000000000000000000
      center := (135)
      previous := (0)
      next := (108)
      square := (1888712109191411653991155020000000000000)
      linear := (-306300824029873807463619785925000000000000)
      constant := (12694976709415087842975010136512590563925473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147510200526130596333/25000000000000000000)
  centralHi := (590040802104522385333/100000000000000000000)
  directionLo := (592129448643299013509/100000000000000000000)
  directionHi := (59212944864329901351/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree143.table
  base := (86548376219605349489087375340244082394997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2915096680187816285750590527308280000000000000)
      constant := (121167218092148802463544857513782080644018098877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree143.table
  base := (86548376219561194843005239227054935663489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2467195144320691896633324109800000000000000)
      constant := (102978114423762929697087250666130483262914203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592129448643299013509/100000000000000000000)
  centralHi := (59212944864329901351/10000000000000000000)
  directionLo := (118842150729963890157/20000000000000000000)
  directionHi := (297105376824909725393/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree144.table
  base := (22126276521405570701013481961125971680957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-733732668904284590833259077472910000000000000)
      constant := (30711914667206721492187005552627957258629543237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree144.table
  base := (22126276521396303261048866934760795172853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (10)
      previous := (0)
      next := (8)
      square := (139904600680845307703048520000000000000)
      linear := (-22999849040762901236645277150000000000000)
      constant := (966724755425018432893160510934760795172853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118842150729963890157/20000000000000000000)
  centralHi := (297105376824909725393/50000000000000000000)
  directionLo := (298142396999971959521/50000000000000000000)
  directionHi := (596284793999943919043/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree145.table
  base := (11310189865486139250864910390202189746743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-369345583880807555114435261559375000000000000)
      constant := (15567462443443626521382966634405343361675392463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree145.table
  base := (45240759461928996909114103502911489746851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (540)
      previous := (0)
      next := (432)
      square := (7554848436765646615964620080000000000000)
      linear := (-1250386124242047385241027877300000000000000)
      constant := (52922145580835245708907852027078610223164977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/50000000000000000000)
  centralHi := (596284793999943919043/100000000000000000000)
  directionLo := (598351645237167114583/100000000000000000000)
  directionHi := (74793955654645889323/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree146.table
  base := (46238807365975474511818154498046835828881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1487299333237891259248963937529180000000000000)
      constant := (63121670364118261904732722972969958666793176121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree146.table
  base := (92477614731924824760904801883022496185491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2517560800565796207406421577000000000000000)
      constant := (107292167151002154458236993596841607397008257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598351645237167114583/100000000000000000000)
  centralHi := (74793955654645889323/12500000000000000000)
  directionLo := (300205690802362134019/50000000000000000000)
  directionHi := (600411381604724268039/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree147.table
  base := (94493393507393315182379974634689432015417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-2994432661905104596080373657641720000000000000)
      constant := (127958582210812058765075215009675404091205976097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree147.table
  base := (94493393507371385844538545754198521344801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-281594372516388627147865266600000000000000)
      constant := (12083322394870199248108629192262595564034403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300205690802362134019/50000000000000000000)
  centralHi := (600411381604724268039/100000000000000000000)
  directionLo := (2409856304306837173/400000000000000000)
  directionHi := (602464076076709293251/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree148.table
  base := (96528855247841204610242322220803366106869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3014266657334426673662819440225080000000000000)
      constant := (129685423995199519410637196390047480653430189629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree148.table
  base := (4826442762391139872221736186492892218803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-637784476182299770313788305450000000000000)
      constant := (27554373592523821498042738538176540449538405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2409856304306837173/400000000000000000)
  centralHi := (602464076076709293251/100000000000000000000)
  directionLo := (120901960077648385289/20000000000000000000)
  directionHi := (302254900194120963223/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree149.table
  base := (12322999993869768946293580798544118558587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-379262581595468593905658152851055000000000000)
      constant := (16427983260165505380934523456552687102735686067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree149.table
  base := (3943359998037708062745803556901016430371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2567926456810900518179519044200000000000000)
      constant := (111694945599729551070034265197908186090500425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120901960077648385289/20000000000000000000)
  centralHi := (302254900194120963223/50000000000000000000)
  directionLo := (75818578133089892377/12500000000000000000)
  directionHi := (606548625064719139017/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree150.table
  base := (20131765522889068309985094415396137559977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3053934648193070828827711005391800000000000000)
      constant := (133173908469111973359788413882388538217796115285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree150.table
  base := (100658827614432374218663499603691001991709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-287190556543622439455987207400000000000000)
      constant := (12575806138074724768734214448811073005975127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75818578133089892377/12500000000000000000)
  centralHi := (606548625064719139017/100000000000000000000)
  directionLo := (608580619450184570507/100000000000000000000)
  directionHi := (152145154862546142627/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree151.table
  base := (51376669118020375079227893236626056411543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1536884321811196453205078393987580000000000000)
      constant := (67467775579245416412038659736196675473482249263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree151.table
  base := (102753338236029867038760968356932827492359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2601503560974303392028250689000000000000000)
      constant := (114679423298863128932287266016637186342293693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608580619450184570507/100000000000000000000)
  centralHi := (152145154862546142627/25000000000000000000)
  directionLo := (122121170346969653691/20000000000000000000)
  directionHi := (76325731466856033557/12500000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree152.table
  base := (10486753181351831010687493269600654561857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1546801319525857491996301285279260000000000000)
      constant := (68354397074694648009166991875653332864082300685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree152.table
  base := (20973506362701835321568204820133557594019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2618292113056004828952616511400000000000000)
      constant := (116186449768241267018702668410718030275192565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122121170346969653691/20000000000000000000)
  centralHi := (76325731466856033557/12500000000000000000)
  directionLo := (612624388981787634131/100000000000000000000)
  directionHi := (153156097245446908533/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree153.table
  base := (107001408344687104719691615600557862753041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3113436634481037061575048353141880000000000000)
      constant := (138493637441737163781358990131397594480470186681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree153.table
  base := (53500704172339719947733265068109331424239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-48797790095142708627351524700000000000000)
      constant := (2179691382421255256963561750568109331424239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612624388981787634131/100000000000000000000)
  centralHi := (153156097245446908533/25000000000000000000)
  directionLo := (307318148576429577/50000000000000000)
  directionHi := (614636297152859154001/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree154.table
  base := (13644370978423823323363014041995389284801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-391658828738794892394686766965655000000000000)
      constant := (17536260129433167272198559176349884268074308841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree154.table
  base := (109154967827384154547617827156150957290973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2651869217219407702801348156200000000000000)
      constant := (119230077946324453940717733575216075846856271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307318148576429577/50000000000000000)
  centralHi := (614636297152859154001/100000000000000000000)
  directionLo := (616641641133849242077/100000000000000000000)
  directionHi := (308320820566924621039/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree155.table
  base := (111328210259505820095747895680266001393449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3153104625339681216739939918308600000000000000)
      constant := (142098124930505798227053845372792402950647499409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree155.table
  base := (27832052564875105697896505297888102302659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-667164442325277284931428494650000000000000)
      constant := (30191669913728489743223931351792978762171793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616641641133849242077/100000000000000000000)
  centralHi := (308320820566924621039/50000000000000000000)
  directionLo := (618640484758891324679/100000000000000000000)
  directionHi := (15466012118972283117/2500000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree156.table
  base := (113521135638942746697106285085665652969521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3172938620769003294322385700891960000000000000)
      constant := (143917769126791576363782858455945493186796422361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree156.table
  base := (113521135638938217856355937834586951209873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (120)
      previous := (0)
      next := (96)
      square := (1678855208170143692436582240000000000000)
      linear := (-298382924598090064072231089000000000000000)
      constant := (13590348864051096472194322257503760853629619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618640484758891324679/100000000000000000000)
  centralHi := (15466012118972283117/2500000000000000000)
  directionLo := (124126578166835032621/20000000000000000000)
  directionHi := (310316445417087581553/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree157.table
  base := (115733743963643471860730023372814885262117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3192772616198325371904831483475320000000000000)
      constant := (145749013624256735589131796210974881738683490797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree157.table
  base := (115733743963639671897546706285843709706523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2702234873464512013574445623400000000000000)
      constant := (123869458310906619339478974794717780162076121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124126578166835032621/20000000000000000000)
  centralHi := (310316445417087581553/50000000000000000000)
  directionLo := (622618921160973328307/100000000000000000000)
  directionHi := (155654730290243332077/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree158.table
  base := (117966035231581572759657491893649508547373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3212606611627647449487277266058680000000000000)
      constant := (147591858422836347289301981414777943903366378293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree158.table
  base := (117966035231578384496670015155830392791897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2719023425546213450498811445800000000000000)
      constant := (125435635258199499430786764431207420605381219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622618921160973328307/100000000000000000000)
  centralHi := (155654730290243332077/25000000000000000000)
  directionLo := (156149659139502177939/25000000000000000000)
  directionHi := (624598636558008711757/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree159.table
  base := (30054502360190356449857196418051463924891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 80102500000000000000000000000000000000000000
      center := (318978)
      previous := (0)
      next := (257760)
      square := (4482683310414964504113377629320000000000000)
      linear := (-808110151764242381767430762160510000000000000)
      constant := (37361575880616617422175831063004956955617432531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree159.table
  base := (60109004720379375437497620426111079645567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-151989554312661938190176514900000000000000)
      constant := (7056203923238034844147030132778333238936701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156149659139502177939/25000000000000000000)
  centralHi := (624598636558008711757/100000000000000000000)
  directionLo := (313286048441592987813/50000000000000000000)
  directionHi := (626572096883185975627/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree160.table
  base := (3062241664730438829338382185334612088571/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-406534325310786450581521103903175000000000000)
      constant := (18914043615385515864117185264493531529649517055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree160.table
  base := (30622416647303827256057136406687640062443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-688150132427404081086885772650000000000000)
      constant := (32149391097777233789208593762980566281685961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313286048441592987813/50000000000000000000)
  centralHi := (626572096883185975627/100000000000000000000)
  directionLo := (314269680527354455289/50000000000000000000)
  directionHi := (628539361054708910579/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree161.table
  base := (62390503337506993842231669729922623948139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1636054298957806841117307306904380000000000000)
      constant := (76594997312313644318514459950782190793922321699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree161.table
  base := (124781006675012105010823793851478208357793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2769389081791317761271908913000000000000000)
      constant := (130193316576620152561144516754989911625660411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/50000000000000000000)
  centralHi := (628539361054708910579/100000000000000000000)
  directionLo := (63050048707160477831/10000000000000000000)
  directionHi := (630500487071604778311/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree162.table
  base := (127092029696243655120863689315061392377149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3291942593344935759817060396392120000000000000)
      constant := (155079240627034850296171796209627002073156231109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree162.table
  base := (63546014848121037879567684726552357889113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (20)
      previous := (0)
      next := (16)
      square := (279809201361690615406097040000000000000)
      linear := (-51595882108759614781412495100000000000000)
      constant := (2440720873606792383417306219726552357889113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63050048707160477831/10000000000000000000)
  centralHi := (630500487071604778311/100000000000000000000)
  directionLo := (632455532033675866399/100000000000000000000)
  directionHi := (790569415042094833/125000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree163.table
  base := (64711367825513886763404089879234398252401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1655888294387128918699753089487740000000000000)
      constant := (78490043465123306918858108477316009354405180441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree163.table
  base := (129422735651026448661713995017178273750731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2802966185954720635120640557800000000000000)
      constant := (133414396185498116726603301892463813391269737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632455532033675866399/100000000000000000000)
  centralHi := (790569415042094833/125000000000000000)
  directionLo := (25376182086435906903/4000000000000000000)
  directionHi := (4956285563757013067/781250000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree164.table
  base := (16471640567189408592452280222789228928687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40051250000000000000000000000000000000000000
      center := (159489)
      previous := (0)
      next := (128880)
      square := (2241341655207482252056688814660000000000000)
      linear := (-416451323025447489372743995194855000000000000)
      constant := (19861566691775408624301974763375249684104060167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree164.table
  base := (131773124537514157403602901691296690771307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2819754738036422072045006380200000000000000)
      constant := (135039723608764157836846982077665010650825289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25376182086435906903/4000000000000000000)
  centralHi := (4956285563757013067/781250000000000000)
  directionLo := (636347602812282362419/100000000000000000000)
  directionHi := (31817380140614118121/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree165.table
  base := (134143196353882205609071893777569999440229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3351444579632901992564397744142200000000000000)
      constant := (160816580438846375060122277154002120352064377389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree165.table
  base := (33535799088470318355539979467292844307271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (30)
      previous := (0)
      next := (24)
      square := (419713802042535923109145560000000000000)
      linear := (-78792869169947875249149227850000000000000)
      constant := (3796525262347657387890951049651878532921813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636347602812282362419/100000000000000000000)
  centralHi := (31817380140614118121/5000000000000000000)
  directionLo := (12765694770084508133/2000000000000000000)
  directionHi := (638284738504225406651/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree166.table
  base := (136532951098331234343510360843902371586229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3371278575062224070146843526725560000000000000)
      constant := (162752227644118343150161115289050755887994363389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree166.table
  base := (136532951098330452455254760211857718742299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2853331842199824945893738025000000000000000)
      constant := (138319953692704112813207551371720158406042073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12765694770084508133/2000000000000000000)
  centralHi := (638284738504225406651/100000000000000000000)
  directionLo := (3201080064641762999/500000000000000000)
  directionHi := (640216012928352599801/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree167.table
  base := (27788477753818210291593954442958755469669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1275912)
      previous := (0)
      next := (1031040)
      square := (17930733241659858016453510517280000000000000)
      linear := (-3391112570491546147729289309308920000000000000)
      constant := (164699475149962418929570585128917927420018322145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree167.table
  base := (34735597192272598914781470149544349171283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (270)
      previous := (0)
      next := (216)
      square := (3777424218382823307982310040000000000000)
      linear := (-717530098570381595704525961850000000000000)
      constant := (34993714088320418328866340257787697427624641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3201080064641762999/500000000000000000)
  centralHi := (640216012928352599801/100000000000000000000)
  directionLo := (642141478968883989513/100000000000000000000)
  directionHi := (321070739484441994757/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree168.table
  base := (14137150936441587482638071339757660578409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1705473282960434112655867545946140000000000000)
      constant := (83329161478161332896624648281922036012964013845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree168.table
  base := (70685754682207662401557751840680630106343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (60)
      previous := (0)
      next := (48)
      square := (839427604085071846218291120000000000000)
      linear := (-160383830353512656652359426100000000000000)
      constant := (7868867634788956192145550379522041890319029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell217.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642141478968883989513/100000000000000000000)
  centralHi := (321070739484441994757/50000000000000000000)
  directionLo := (161015297179882650819/25000000000000000000)
  directionHi := (644061188719530603277/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree169.table
  base := (71910156441292466182231125708096424524693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 160205000000000000000000000000000000000000000
      center := (637956)
      previous := (0)
      next := (515520)
      square := (8965366620829929008226755258640000000000000)
      linear := (-1715390280675095151447090437237820000000000000)
      constant := (84314385531571974241422402110171657538195688413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 5
  qDenominator := 9
  table := BinomialMassData.Q5_9.Degree169.table
  base := (143820312882584471072258925095900192918863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (1080)
      previous := (0)
      next := (864)
      square := (15109696873531293231929240160000000000000)
      linear := (-2903697498444929256666835492200000000000000)
      constant := (143314236911416266484667141754589305208809301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5_9.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell217.Kernel169
