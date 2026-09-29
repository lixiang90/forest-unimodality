import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell193.Parameters
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch150_199
import ForestUnimodality.BinomialMassData.Q113_213.Batch000_049
import ForestUnimodality.BinomialMassData.Q113_213.Batch050_099
import ForestUnimodality.BinomialMassData.Q113_213.Batch100_149
import ForestUnimodality.BinomialMassData.Q113_213.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree000.table
  base := (439714411298969487190646533/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77319963789037413764981821250000000000)
      linear := (-5910288542023926913401843375000000000)
      constant := (109928602824742371797661633250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree000.table
  base := (439714411298969487190646533/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77319963789037413764981821250000000000)
      linear := (-5910288542023926913401843375000000000)
      constant := (109928602824742371797661633250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree001.table
  base := (489502764800452476505037904712734849158209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-9960592249780852571227557742696871750000000000)
      constant := (6934260865952910405072169123865875754308809677321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree001.table
  base := (489401270903346496400748445723093384015149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-31921378381918132511622585147303000000000000)
      constant := (22212682686434248736271506008760896739383294981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49906787853214316469/100000000000000000000)
  directionHi := (4990678785321431647/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree002.table
  base := (57592993973618594996006219679583253759149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-19251659022811125885355767748581500500000000000)
      constant := (4088198397859893629030497282895048514528425680905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree002.table
  base := (71965077087722347429842225978613258570323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-15424401429232899175543036109490750000000000)
      constant := (3273450990273524826022947049300806428076984187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/100000000000000000000)
  centralHi := (4990678785321431647/10000000000000000000)
  directionLo := (70578856236492527093/100000000000000000000)
  directionHi := (35289428118246263547/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree003.table
  base := (90590330948890567583473120395594717440329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-14271362897920699599741988877233064625000000000)
      constant := (1294394548057026800950174385654874648200587305601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree003.table
  base := (90548917124813950936095652785490632571783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-5081879613996947827373427984923500000000000)
      constant := (460595958676566633476823289151413778794358103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/100000000000000000000)
  centralHi := (35289428118246263547/50000000000000000000)
  directionLo := (86441092204328492787/100000000000000000000)
  directionHi := (21610273051082123197/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree004.table
  base := (24495326421137353731461827077642232042419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-37833792568871672513612187760350758000000000000)
      constant := (1775132436564070388515887934469269335164341044055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree004.table
  base := (122416355161868645485929384452076357196793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-121250060386958525083271263019283000000000000)
      constant := (5684833991911837740005974418257704249661301617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441092204328492787/100000000000000000000)
  centralHi := (21610273051082123197/25000000000000000000)
  directionLo := (49906787853214316469/50000000000000000000)
  directionHi := (99813575706428632939/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree005.table
  base := (5532309159326307007609954854423062006551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-5890607417737743228467549720779423343750000000)
      constant := (164598456351255996324820920808807090361302846738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree005.table
  base := (88473850996051373854441536903484742551627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-151026287721971989273820822309943000000000000)
      constant := (4217120058761017483550315421610164284824765363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/50000000000000000000)
  centralHi := (99813575706428632939/100000000000000000000)
  directionLo := (4463798807137920317/4000000000000000000)
  directionHi := (55797485089224003963/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree006.table
  base := (16893709600025452589289378885565580254399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-14103981528733054785467151943030003875000000000)
      constant := (261925434684980678713826835777185625743165333431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree006.table
  base := (33771732758951828376906468582042454820481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-10044584169832525192465021200033500000000000)
      constant := (186419428679612930354836138045917014750044721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/4000000000000000000)
  centralHi := (55797485089224003963/50000000000000000000)
  directionLo := (122246164941704573117/100000000000000000000)
  directionHi := (61123082470852286559/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree007.table
  base := (53709138262641140244828237250375383623671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-65706992887962492455996817778004644250000000000)
      constant := (883746737653120094599054145792949325340076260399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree007.table
  base := (13421354584808637176726484962519000470087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-52644685597999729413729985222815750000000000)
      constant := (707660266974012130790980443622267282327377103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246164941704573117/100000000000000000000)
  centralHi := (61123082470852286559/50000000000000000000)
  directionLo := (6602047469683208113/5000000000000000000)
  directionHi := (132040949393664162261/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree008.table
  base := (8774028424872182818242537249620494579791/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-74998059660992765770125027783889273000000000000)
      constant := (781738323332973695309095570387619934567122723395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree008.table
  base := (43851391047034444176796896369506695719541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-240354969727012381845469500181923000000000000)
      constant := (2504094955670232020276240277629613278099855629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6602047469683208113/5000000000000000000)
  centralHi := (132040949393664162261/100000000000000000000)
  directionLo := (70578856236492527093/50000000000000000000)
  directionHi := (141157712472985054187/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree009.table
  base := (7292023052613157085928337586034320486587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-84289126434023039084253237789773901750000000000)
      constant := (719052302096029360003843237391594712115233266015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree009.table
  base := (36444671519632349154854955075586793620357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-30014577451336205115113228830287000000000000)
      constant := (255941127478610212282936987320546026640219637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/50000000000000000000)
  centralHi := (141157712472985054187/100000000000000000000)
  directionLo := (4678761361238842169/3125000000000000000)
  directionHi := (149720363559642949409/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree010.table
  base := (30616090214570079656325397981541472603861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-93580193207053312398381447795658530500000000000)
      constant := (683468908807916488914624910820199613360791812509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree010.table
  base := (30602958765108091125287707959831867571773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-299907424397039310226568618763243000000000000)
      constant := (2189644909105401887105513840318041999863769237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/3125000000000000000)
  centralHi := (149720363559642949409/100000000000000000000)
  directionLo := (39454780079745565941/25000000000000000000)
  directionHi := (31563824063796452753/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree011.table
  base := (50491307949396855011500786402285997473/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-12858907497510448214063707225192894906250000000)
      constant := (83512372019356022823092602915855834894225500468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree011.table
  base := (5168028067104991540219152664823028491201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-329683651732052774417118178053903000000000000)
      constant := (2140564805413521245667707738976682898086490845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39454780079745565941/25000000000000000000)
  centralHi := (31563824063796452753/20000000000000000000)
  directionLo := (82761044900489174029/50000000000000000000)
  directionHi := (165522089800978348059/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree012.table
  base := (10938301861915593573427157493540402551339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-56081163376556929513318933903713894000000000000)
      constant := (334418807039665846012874998361439943642491416291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree012.table
  base := (10933280523816637835420631255640659899921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-19969993281503679922648207630253500000000000)
      constant := (119060470567944197905738354024686566555501761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/50000000000000000000)
  centralHi := (165522089800978348059/100000000000000000000)
  directionLo := (6915287376346279423/4000000000000000000)
  directionHi := (21610273051082123197/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree013.table
  base := (9253541864277940107191755594051364078029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-60726696763072066170383038906656208375000000000)
      constant := (341538481706014740908972759763284410951201076901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree013.table
  base := (4624545965998224047155022644575452245831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-97309026600519925699554324158805750000000000)
      constant := (547216581795550681005609487467700942941106639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/4000000000000000000)
  centralHi := (21610273051082123197/12500000000000000000)
  directionLo := (44985370649616901703/25000000000000000000)
  directionHi := (179941482598467606813/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree014.table
  base := (7809022811242166198947711680127189411643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-65372230149587202827447143909598522750000000000)
      constant := (354523897561288524571813061215035522454500447667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree014.table
  base := (15610136848753818598024444162788694939131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-419012333737093166988766855925883000000000000)
      constant := (2272233061433564051044584840507842300693434339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44985370649616901703/25000000000000000000)
  centralHi := (179941482598467606813/100000000000000000000)
  directionLo := (466835253552848399/250000000000000000)
  directionHi := (186734101421139359601/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree015.table
  base := (3279887161723912438094832677405458483687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-35008881768051169742255624456270418562500000000)
      constant := (186369133216874577977590823044937808192507288103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree015.table
  base := (3278129600763694726272117219790360390409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-12466348918669628643869900422681750000000000)
      constant := (66364164648287301589652616576001956728051769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/250000000000000000)
  centralHi := (186734101421139359601/100000000000000000000)
  directionLo := (9664407910910282537/5000000000000000000)
  directionHi := (193288158218205650741/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree016.table
  base := (2188737008090777730271361175354113138117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-149326593845234952283150707830966303000000000000)
      constant := (791401591269864642592749622511792727404285308865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree016.table
  base := (10937442324507820725265625447620124046247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-478564788407120095369865974507203000000000000)
      constant := (2536416995780399949360674077970245407854180143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9664407910910282537/5000000000000000000)
  centralHi := (193288158218205650741/100000000000000000000)
  directionLo := (199627151412857265877/100000000000000000000)
  directionHi := (99813575706428632939/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree017.table
  base := (28241737420685185062454871085520590451/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-19827207577283153199659864729606366468750000000)
      constant := (105758885242981324167316179632524622086770661260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree017.table
  base := (9031822305046752148624678613025364128737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-508341015742133559560415533797863000000000000)
      constant := (2711745794049080266682454271919948745156668953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199627151412857265877/100000000000000000000)
  centralHi := (99813575706428632939/50000000000000000000)
  directionLo := (205770957754095076591/100000000000000000000)
  directionHi := (12860684859630942287/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree018.table
  base := (7358033828743227191323277748258885064349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-167908727391295498911407127842735560500000000000)
      constant := (908882806593905029325508490698489694294007714981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree018.table
  base := (7353138803470051480309347986194260800529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-59790804786349669305662788120947000000000000)
      constant := (323685250342179107935433354845371268695466689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/100000000000000000000)
  centralHi := (12860684859630942287/6250000000000000000)
  directionLo := (211736568709477581279/100000000000000000000)
  directionHi := (1323353554434234883/625000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree019.table
  base := (2935558935062110628686326067458899636561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-88599897082162886112767668924310094625000000000)
      constant := (489673406498724937133446905869307571521023588809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree019.table
  base := (5866797093792641378254565388528640767663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-567893470412160487941514652379183000000000000)
      constant := (3139111844748778089637861764840602902988102647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211736568709477581279/100000000000000000000)
  centralHi := (1323353554434234883/625000000000000000)
  directionLo := (5438466121222110087/2500000000000000000)
  directionHi := (217538644848884403481/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree020.table
  base := (181926912670042306813556227234889955417/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-186490860937356045539663547854504818000000000000)
      constant := (1057060452755644106403857991496560518502679636825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree020.table
  base := (2272183491934039845313986707192169838749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-298834848873586976066032105834921500000000000)
      constant := (1694144859834543343676428381240031553414203381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5438466121222110087/2500000000000000000)
  centralHi := (217538644848884403481/100000000000000000000)
  directionLo := (4463798807137920317/2000000000000000000)
  directionHi := (223189940356896015851/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree021.table
  base := (3365681774425804263269325081777058763829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-195781927710386318853791757860389446750000000000)
      constant := (1141690722672289886801814394574249706395312227101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree021.table
  base := (1681168135996025809687054989040469974947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-34858106949010412017922987275583500000000000)
      constant := (203313008486745261471717051508971509143707827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/2000000000000000000)
  centralHi := (223189940356896015851/100000000000000000000)
  directionLo := (28587704128682158857/12500000000000000000)
  directionHi := (228701633029457270857/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree022.table
  base := (576029386648509031382649901512865785447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-51268248620854148041979991966568518875000000000)
      constant := (308240278586020085257096360995746356579059760543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree022.table
  base := (460236451356010627305863019617013602977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-657222152417200880513163330251163000000000000)
      constant := (3952259418586648583807328969182687450767317565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/12500000000000000000)
  centralHi := (228701633029457270857/100000000000000000000)
  directionLo := (57149312565644759/24414062500000000)
  directionHi := (46816716853776186573/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree023.table
  base := (1347224215273162054358339233887541273551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-214364061256446865482048177872158704250000000000)
      constant := (1330641441225131838594514109860374172967019890119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree023.table
  base := (84040835504975303162819189824433351167/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-85874797469026793087964111192727875000000000)
      constant := (533178524957317560223710245076046808418191246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57149312565644759/24414062500000000)
  centralHi := (46816716853776186573/20000000000000000000)
  directionLo := (239344546413725543619/100000000000000000000)
  directionHi := (11967227320686277181/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree024.table
  base := (481446400771431784127250847305953951257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-223655128029477138796176387878043333000000000000)
      constant := (1434539756848150027833151350981291564656016882433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree024.table
  base := (59899801756584730370011329244711925203/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-9955202876211497345753645122673375000000000)
      constant := (63868412388258206478168395060543592814948323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/100000000000000000000)
  centralHi := (11967227320686277181/5000000000000000000)
  directionLo := (48898465976681829247/20000000000000000000)
  directionHi := (61123082470852286559/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree025.table
  base := (-152266126470868708622947855966709299591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-116473097401253706055152298941963980875000000000)
      constant := (772247909849638844044758453119580381400951059121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree025.table
  base := (-15324748281781227897783040426851372597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-186637708605560318271203002030785750000000000)
      constant := (1237759666249691452657776949030577150383233535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/20000000000000000000)
  centralHi := (61123082470852286559/25000000000000000000)
  directionLo := (249533939266071582347/100000000000000000000)
  directionHi := (62383484816517895587/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree026.table
  base := (-510083280298753072375524316010174474069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-121118630787768842712216403944906295250000000000)
      constant := (830187874002028947886206277993985391868321842339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree026.table
  base := (-1021877814224038418295717873326052649573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-776327061757254737275361567413803000000000000)
      constant := (5322538334410367097813310672116268317341522563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/100000000000000000000)
  centralHi := (62383484816517895587/25000000000000000000)
  directionLo := (254475685124275166203/100000000000000000000)
  directionHi := (63618921281068791551/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree027.table
  base := (-1673360803777918886220250364477575017953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-251528328348567958738561017895697219250000000000)
      constant := (1782067615799465313568618135498985351137169985943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree027.table
  base := (-1674850890162551221750467175496002412829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-89567032121363133496212347411607000000000000)
      constant := (634740694519919693980798213555683651836929011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254475685124275166203/100000000000000000000)
  centralHi := (63618921281068791551/25000000000000000000)
  directionLo := (129661638306492739181/50000000000000000000)
  directionHi := (259323276612985478363/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree028.table
  base := (-2270726163953207075118918732114667689633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-260819395121598232052689227901581848000000000000)
      constant := (1909477807638591795911151072745608886510957172023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree028.table
  base := (-2272022114464208929606912567932603906909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-835879516427281665656460685995123000000000000)
      constant := (6121122619037055372455097467975389693347445579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129661638306492739181/50000000000000000000)
  centralHi := (259323276612985478363/100000000000000000000)
  directionLo := (264081898787328324521/100000000000000000000)
  directionHi := (132040949393664162261/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree029.table
  base := (-2817794449768765480205152326657119201251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-270110461894628505366817437907466476750000000000)
      constant := (2042527992176142891802680771550346418158703328581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree029.table
  base := (-2818920303106432362475865742698614624337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-865655743762295129847010245285783000000000000)
      constant := (6547656602631621872486759394381783553108454647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/100000000000000000000)
  centralHi := (132040949393664162261/50000000000000000000)
  directionLo := (268756277584257483033/100000000000000000000)
  directionHi := (134378138792128741517/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree030.table
  base := (-3319195891823299055301504434316751119943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-279401528667658778680945647913351105500000000000)
      constant := (2181152604564331967915942681368933182891917849633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree030.table
  base := (-830043239836502802364757815057007817797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-24873110308258572056598883460456750000000000)
      constant := (194223840451881095958814290750500123590485323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/100000000000000000000)
  centralHi := (134378138792128741517/50000000000000000000)
  directionLo := (136675367399151520703/50000000000000000000)
  directionHi := (273350734798303041407/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree031.table
  base := (-3778807248282475686370326027845002546227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-288692595440689051995073857919235734250000000000)
      constant := (2325296749252361036987837184789894408054057867637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree031.table
  base := (-3779654371117224244072339556061438689193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-925208198432322058228109363867103000000000000)
      constant := (7454151807376057824871118437954011588110002783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/50000000000000000000)
  centralHi := (273350734798303041407/100000000000000000000)
  directionLo := (277869234872444886367/100000000000000000000)
  directionHi := (8683413589763902699/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree032.table
  base := (-4199875300489797807290586915008149623337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-297983662213719325309202067925120363000000000000)
      constant := (2474914451267700057502726743789362110956261736047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree032.table
  base := (-4200609094358751098428973086113665897901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-954984425767335522418658923157763000000000000)
      constant := (7933790053698255027318828332347405091878129531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277869234872444886367/100000000000000000000)
  centralHi := (8683413589763902699/3125000000000000000)
  directionLo := (282315424945970108373/100000000000000000000)
  directionHi := (141157712472985054187/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree033.table
  base := (-114627997621167923436475116490552447103/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-38409341123343699827916284741375623968750000000)
      constant := (328745899623006093012580882452304348045672610465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree033.table
  base := (-2292877494979154568010630830293685556737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-54708925172352721478289360136023500000000000)
      constant := (468380538255760900710897813279950031108488783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315424945970108373/100000000000000000000)
  centralHi := (141157712472985054187/50000000000000000000)
  directionLo := (286692669310272775609/100000000000000000000)
  directionHi := (28669266931027277561/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree034.table
  base := (-1234205009153049253603465956068582774079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-79141448939944967984364621984222405125000000000)
      constant := (697605678931648337165287644725195645211365040649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree034.table
  base := (-493736925109316557987287985985443681753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-507268440218681225399879020869541500000000000)
      constant := (4472613699057560972330877132996103028012740715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286692669310272775609/100000000000000000000)
  centralHi := (28669266931027277561/10000000000000000000)
  directionLo := (291004079198342443877/100000000000000000000)
  directionHi := (145502039599171221939/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree035.table
  base := (-21027542674433565325691334583038138741/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-162928431266405072625793348971387124625000000000)
      constant := (1478126980978693386803830271503645868236030346375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree035.table
  base := (-1314340066203930794338967206520217213661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-261078276943093978747576900257435750000000000)
      constant := (2369209150155087940667521769656948015233414091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291004079198342443877/100000000000000000000)
  centralHi := (145502039599171221939/50000000000000000000)
  directionLo := (147626269328921352967/50000000000000000000)
  directionHi := (59050507731568541187/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree036.table
  base := (-5546917842858737607132954700763679389437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-335147929305840418565714907948658878000000000000)
      constant := (3127438264650801038883160406022231445658755265147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree036.table
  base := (-5547327666547487037558419951022071819991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-119343259456376597686761906702267000000000000)
      constant := (1113956080251105266836326324632589735955425369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147626269328921352967/50000000000000000000)
  centralHi := (59050507731568541187/20000000000000000000)
  directionLo := (4678761361238842169/1562500000000000000)
  directionHi := (299440727119285898817/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree037.table
  base := (-5808258894111997384429462828108143778387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-344438996078870691879843117954543506750000000000)
      constant := (3303956616119939108499694480863034227048304032597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree037.table
  base := (-5808612546888780328970621233642570904969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1103865562442402843371406719611063000000000000)
      constant := (10591470919094462799401076992763731200612461439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/1562500000000000000)
  centralHi := (299440727119285898817/100000000000000000000)
  directionLo := (37946392395134296379/12500000000000000000)
  directionHi := (303571139161074371033/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree038.table
  base := (-3021017227296694947784299759365531414103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-176865031425950482596985663980214067750000000000)
      constant := (1742896538611130016033232068356602060417117536593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree038.table
  base := (-6042339440394885657051449005469640530347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1133641789777416307561956278901723000000000000)
      constant := (11174384172115659339765438994654001878778686957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37946392395134296379/12500000000000000000)
  centralHi := (303571139161074371033/100000000000000000000)
  directionLo := (38455762735694544411/12500000000000000000)
  directionHi := (307646101885556355289/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree039.table
  base := (-249967543856127918158046449154468868733/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-363021129624931238508099537966312764250000000000)
      constant := (3672934279737275619997918631017933346126610103075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree039.table
  base := (-6249451452937398220699211637278598350873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-129268668568047752416945093132487000000000000)
      constant := (1308255743728138735560133952765601585713249207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38455762735694544411/12500000000000000000)
  centralHi := (307646101885556355289/100000000000000000000)
  directionLo := (311667790249816898957/100000000000000000000)
  directionHi := (155833895124908449479/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree040.table
  base := (-3215256620804382815729238655583548118517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-186156098198980755911113873986098696500000000000)
      constant := (1932684504957338725427535096099398462522167250627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree040.table
  base := (-6430739657811253170362441605305476359099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1193194244447443235943055397483043000000000000)
      constant := (12391187593202912727387677263558615843064037469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667790249816898957/100000000000000000000)
  centralHi := (155833895124908449479/50000000000000000000)
  directionLo := (315638240637964527529/100000000000000000000)
  directionHi := (31563824063796452753/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree041.table
  base := (-6586672782068205944240560041319590235319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-381603263170991785136355957978082021750000000000)
      constant := (4063087859853472420308134917080199030421195691089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree041.table
  base := (-6586867702678227993904009864267609788617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1222970471782456700133604956773703000000000000)
      constant := (13025011762033884478958003468314035811500235327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638240637964527529/100000000000000000000)
  centralHi := (31563824063796452753/10000000000000000000)
  directionLo := (31955936291533587571/10000000000000000000)
  directionHi := (319559362915335875711/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree042.table
  base := (-6718224694725483922437142046557359135603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-390894329944022058450484167983966650500000000000)
      constant := (4266082935585920380000244098045633378227417603093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree042.table
  base := (-6718392413094142939847957333212581489729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-139194077679718907147128279562707000000000000)
      constant := (1519527659714169096210766330744489376710276111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31955936291533587571/10000000000000000000)
  centralHi := (319559362915335875711/100000000000000000000)
  directionLo := (4042911889589163311/1250000000000000000)
  directionHi := (323432951167133064881/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree043.table
  base := (-6825636808073457152677962186435243280571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-400185396717052331764612377989851279250000000000)
      constant := (4474347612581499451211788492417936164442562723501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree043.table
  base := (-6825781048292250121374688052373531883941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1282522926452483628514704075355023000000000000)
      constant := (14343377920299671473081476037816384231957480771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4042911889589163311/1250000000000000000)
  centralHi := (323432951167133064881/100000000000000000000)
  directionLo := (327260693292834698533/100000000000000000000)
  directionHi := (163630346646417349267/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree044.table
  base := (-6909301767208631122841215146053705776699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-409476463490082605078740587995735908000000000000)
      constant := (4687876330919286094924985412041183049500665897869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree044.table
  base := (-6909425756600988052452206716227388391241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1312299153787497092705253634645683000000000000)
      constant := (15027880919272820373571526246678251616077787071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327260693292834698533/100000000000000000000)
  centralHi := (163630346646417349267/50000000000000000000)
  directionLo := (82761044900489174029/25000000000000000000)
  directionHi := (331044179601956696117/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree045.table
  base := (-696954915469930370847649058576958775663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-209383765131556439196434399000810268375000000000)
      constant := (2453332211827206879589855849722034281328675414765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree045.table
  base := (-3484827843829194522751383545933957516717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-74559743395695030938655732996463500000000000)
      constant := (873846833397613371076931242895929420158229603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/25000000000000000000)
  centralHi := (331044179601956696117/100000000000000000000)
  directionLo := (13391396421413760951/4000000000000000000)
  directionHi := (10462028454229500743/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree046.table
  base := (-7006655649299930669134446399193339589543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-428058597036143151706997008007505165500000000000)
      constant := (5130707972968960640917706674791884706518930487233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree046.table
  base := (-1401349428677702735457161111732175841571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1371851608457524021086352753227003000000000000)
      constant := (16447451630410339686214185545066372571218826505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13391396421413760951/4000000000000000000)
  centralHi := (10462028454229500743/3125000000000000000)
  directionLo := (84621075904581847989/25000000000000000000)
  directionHi := (338484303618327391957/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree047.table
  base := (-7020853541838269378630642504487462954361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-437349663809173425021125218013389794250000000000)
      constant := (5360003689585548545834745834813824287849071452991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree047.table
  base := (-140418641739903195079402080232493919111/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-700813917896268742638451156258831500000000000)
      constant := (8591248141547062145695862149851045084596326025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84621075904581847989/25000000000000000000)
  centralHi := (338484303618327391957/100000000000000000000)
  directionLo := (21383981233570479847/6250000000000000000)
  directionHi := (342143699737127677553/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree048.table
  base := (-7012337875281074904532823740258958611993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-446640730582203698335253428019274423000000000000)
      constant := (5594548811662805960792463493646334451290173693183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree048.table
  base := (-3506202638453252062269226242517573654907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-79522447951530608303747326211573500000000000)
      constant := (996353784622959252191993246387156911205613813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21383981233570479847/6250000000000000000)
  centralHi := (342143699737127677553/100000000000000000000)
  directionLo := (6915287376346279423/2000000000000000000)
  directionHi := (345764368817313971151/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree049.table
  base := (-3490636216154688335773150186872882537773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-227965898677616985824690819012579525875000000000)
      constant := (2917170510005145118021529841353945412142516686363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree049.table
  base := (-139626604978618614341159957467421251253/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-730590145231282206829000715549491500000000000)
      constant := (9351529865655837929987084781705482631297566075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/2000000000000000000)
  centralHi := (345764368817313971151/100000000000000000000)
  directionLo := (174673757486250107643/50000000000000000000)
  directionHi := (349347514972500215287/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree050.table
  base := (-6927794757261630797498780561244795116073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-465222864128264244963509848031043680500000000000)
      constant := (6079378366976923839759010141622650707817281703663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree050.table
  base := (-1731961083353592152845492859560255010783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-372739129449394469462137747597410750000000000)
      constant := (4872141219212221949130684108980148290415786073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174673757486250107643/50000000000000000000)
  centralHi := (349347514972500215287/100000000000000000000)
  directionLo := (176447140591231317733/50000000000000000000)
  directionHi := (352894281182462635467/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree051.table
  base := (-6852020368832659016854827956728912843581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-474513930901294518277638058036928309250000000000)
      constant := (6329659216798465436755423524539100824675184974811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree051.table
  base := (-342603143186141510110839647292074292947/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-42242576253683092834419459713341750000000000)
      constant := (563635509090706103687948430392365017446270865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176447140591231317733/50000000000000000000)
  centralHi := (352894281182462635467/100000000000000000000)
  directionLo := (178202876776100855249/50000000000000000000)
  directionHi := (356405753552201710499/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree052.table
  base := (-6754046294450917598322039886557632819539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-483804997674324791591766268042812938000000000000)
      constant := (6585182195550130450858290841732042293910381257909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree052.table
  base := (-42213016918204903018210957473848850889/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-193813621558450600778706263621370375000000000)
      constant := (2638749460974973340868129503216948529680339180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178202876776100855249/50000000000000000000)
  centralHi := (356405753552201710499/100000000000000000000)
  directionLo := (2879063721575481709/800000000000000000)
  directionHi := (179941482598467606813/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree053.table
  base := (-6633954035966639920172850194820470097793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-175541496777271294021322348895940750000000000)
      constant := (2437147080509770653165480064766054799299525487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree053.table
  base := (-6633985226166592097761903457456038367539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1580285199802618270420199668261623000000000000)
      constant := (21945913267085768258988664063715425995303123109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2879063721575481709/800000000000000000)
  centralHi := (179941482598467606813/50000000000000000000)
  directionLo := (36332689979241039161/10000000000000000000)
  directionHi := (363326899792410391611/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree054.table
  base := (-6491812058478197375256439063828103093527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-502387131220385338220022688054582195500000000000)
      constant := (7111950108126547837858541722233547719777484873937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree054.table
  base := (-6491838766769695129246994643052739888141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-178895714126403526067861025283587000000000000)
      constant := (2533180884929567678561859063880549138223881219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36332689979241039161/10000000000000000000)
  centralHi := (363326899792410391611/100000000000000000000)
  directionLo := (45842311853139214919/12500000000000000000)
  directionHi := (366738494825113719353/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree055.table
  base := (-1581919469807125790006036020815672150559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-127919549498353902883537724515116706062500000000)
      constant := (1845798314505014151323583590525797415759256740529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree055.table
  base := (-6327700742515328766994274061230354113411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1639837654472645198801298786842943000000000000)
      constant := (23668137174834423983831130714219155064228656341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45842311853139214919/12500000000000000000)
  centralHi := (366738494825113719353/100000000000000000000)
  directionLo := (185059322286406111187/50000000000000000000)
  directionHi := (2960949156582497779/800000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree056.table
  base := (-3070799910519106279520359438458267810729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-260484632383222942424139554033175726500000000000)
      constant := (3829837457286582515764515709390256122352817346799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree056.table
  base := (-6141619386961875011110808180189964046497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1669613881807658662991848346133603000000000000)
      constant := (24554438710182402656349003983002249521174477607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185059322286406111187/50000000000000000000)
  centralHi := (2960949156582497779/800000000000000000)
  directionLo := (466835253552848399/125000000000000000)
  directionHi := (373468202842278719201/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree057.table
  base := (-2966809242154162501080990386443692690391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-265130165769738079081203659036118040875000000000)
      constant := (3970697251438666748433485436633261500227030013921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree057.table
  base := (-5933635223538018926399053118548495390671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-188821123238074680798044211713807000000000000)
      constant := (2828614525766956567989480972180966034735627489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/125000000000000000)
  centralHi := (373468202842278719201/100000000000000000000)
  directionLo := (376787985487949419617/100000000000000000000)
  directionHi := (188393992743974709809/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree058.table
  base := (-1140753596577665843926159342751915675329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-539551398312506431476535528078120710500000000000)
      constant := (8228351539874688000324318318609714372099211146995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree058.table
  base := (-5703782299758318288576482669777538792331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1729166336477685591372947464714923000000000000)
      constant := (26377411695293355378773578945562476842530734861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376787985487949419617/100000000000000000000)
  centralHi := (188393992743974709809/50000000000000000000)
  directionLo := (190039386366282583353/50000000000000000000)
  directionHi := (380078772732565166707/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree059.table
  base := (-5452076981789178928892091232212393204053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-548842465085536704790663738084005339250000000000)
      constant := (8520545619663829050410875375235101751937720535043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree059.table
  base := (-5452089223498563245143824946178491909803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1758942563812699055563497024005583000000000000)
      constant := (27314080302443924733751794037076595000544147693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190039386366282583353/50000000000000000000)
  centralHi := (380078772732565166707/100000000000000000000)
  directionLo := (23958831956781115699/6250000000000000000)
  directionHi := (76668262261699570237/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree060.table
  base := (-129464239214775011691967787652203214913/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-69766691482320872263098993511236246000000000000)
      constant := (1102247050145068907142874231281658141819317998515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree060.table
  base := (-1035716006630847054053291646777958575229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-198746532349745835528227398144027000000000000)
      constant := (3140837273639594730870951664078581554111353055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23958831956781115699/6250000000000000000)
  centralHi := (76668262261699570237/20000000000000000000)
  directionLo := (386576316436411301481/100000000000000000000)
  directionHi := (193288158218205650741/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree061.table
  base := (-4883265985259639221993800936465728235913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-567424598631597251418920158095774596750000000000)
      constant := (9120643597735197357626998998573691895072962550703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree061.table
  base := (-4883274928372601213073120792474311715719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1818495018482725983944596142586903000000000000)
      constant := (29237776259792842061355770038356285951769544689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386576316436411301481/100000000000000000000)
  centralHi := (193288158218205650741/50000000000000000000)
  directionLo := (77956894731221854283/20000000000000000000)
  directionHi := (48723059207013658927/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree062.table
  base := (-570772905347745922304830483402175903971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-72089458175578440591631046012707403187500000000)
      constant := (1178568371063664798114902137283762169142199118901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree062.table
  base := (-4566190883747527582837072162454774755211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1848271245817739448135145701877563000000000000)
      constant := (30224801923433044054644190709929775324130832141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77956894731221854283/20000000000000000000)
  centralHi := (48723059207013658927/12500000000000000000)
  directionLo := (392966440522846534143/100000000000000000000)
  directionHi := (767512579146184637/195312500000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree063.table
  base := (-4227335637421918389149283482415425953939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-586006732177657798047176578107543854250000000000)
      constant := (9741686311045400972732648366864720193699300044309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree063.table
  base := (-4227342164260603942045151972150553645613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-208671941461416990258410584574247000000000000)
      constant := (3469845756276556535649262396036720059072464867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392966440522846534143/100000000000000000000)
  centralHi := (767512579146184637/195312500000000000)
  directionLo := (396122848180992486781/100000000000000000000)
  directionHi := (198061424090496243391/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree064.table
  base := (-3866735184374291538853227345802087157347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-595297798950688071361304788113428483000000000000)
      constant := (10060061455206256195274472178306191137299236888357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree064.table
  base := (-3866740758229447720283303659601790987369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1907823700487766376516244820458883000000000000)
      constant := (32249205365062754374790397933717958344694055839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396122848180992486781/100000000000000000000)
  centralHi := (198061424090496243391/50000000000000000000)
  directionLo := (79850860565142906351/20000000000000000000)
  directionHi := (99813575706428632939/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree065.table
  base := (-871097995514203349640576456474195548897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-151147216430929586168858249529828277937500000000)
      constant := (2595918064499145602925842628394235830648336341407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree065.table
  base := (-3484396740989474998842947375816715533259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-1937599927822779840706794379749543000000000000)
      constant := (33286582142046388224293189377261116432971572429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79850860565142906351/20000000000000000000)
  centralHi := (99813575706428632939/25000000000000000000)
  directionLo := (25147586691391816489/6250000000000000000)
  directionHi := (16094455482490762553/4000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree066.table
  base := (-1540157259076774263410049529465889157711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-306939966248374308994780604062598870250000000000)
      constant := (5356259299614669424631727942041442411057169586841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree066.table
  base := (-1540159290204889499019443309568668494421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-109298675286544072494296885502233500000000000)
      constant := (1907818986292286526613292976391315342119623739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25147586691391816489/6250000000000000000)
  centralHi := (16094455482490762553/4000000000000000000)
  directionLo := (405444661171532560633/100000000000000000000)
  directionHi := (202722330585766280317/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree067.table
  base := (-663627481684559090969786549957092508069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-155792749817444722825922354532770592312500000000)
      constant := (2761650094471208924754696733177803230956249721339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree067.table
  base := (-1327256696780398092159147609778501005639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-998576191246403384543946749165431500000000000)
      constant := (17705841937906346753491204348786334687875164209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405444661171532560633/100000000000000000000)
  centralHi := (202722330585766280317/50000000000000000000)
  directionLo := (408504664289558122133/100000000000000000000)
  directionHi := (204252332144779061067/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree068.table
  base := (-2206984204309008560125148563047971235463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-632462066042809164617817628136966998000000000000)
      constant := (11385917509051646008615653213665631863073705126753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree068.table
  base := (-2206987162355691444423077749870725454401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2026928609827820233278443057621523000000000000)
      constant := (36499408238307577930376001276284959056859281031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408504664289558122133/100000000000000000000)
  centralHi := (204252332144779061067/50000000000000000000)
  directionLo := (205770957754095076591/50000000000000000000)
  directionHi := (411541915508190153183/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree069.table
  base := (-868871195654875265328111301992116435619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-320876566407919718965972919071425813375000000000)
      constant := (5865234960678116262779815123178043290467238590389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree069.table
  base := (-868872457366207965409624122624584192993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-114261379842379649859388478717343500000000000)
      constant := (2089106367368516324632434484467715971083122287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/50000000000000000000)
  centralHi := (411541915508190153183/100000000000000000000)
  directionLo := (207278457451549980743/50000000000000000000)
  directionHi := (414556914903099961487/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree070.table
  base := (-124678872465920024210063397571279868241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-325522099794434855623037024074368127750000000000)
      constant := (6040128777401554940488272714479065296112673536355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree070.table
  base := (-1246790876890288021625298693537065509097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2086481064497847161659542176202843000000000000)
      constant := (38725202807051404370509009166977926874917778207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207278457451549980743/50000000000000000000)
  centralHi := (414556914903099961487/100000000000000000000)
  directionLo := (208775072247503846357/50000000000000000000)
  directionHi := (83510028899001538543/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree071.table
  base := (-734126765924127458612118573659222931031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1737534226267248762126671487130000000000000)
      linear := (-130992911398908943574727684617064250000000000)
      constant := (2466828081523485560448699011944291156849233921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree071.table
  base := (-734128601211136150525157476368833186997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1584)
      previous := (792)
      next := (792)
      square := (5567037392810693791078691130000000000000)
      linear := (-419809024366764654999026331183000000000000)
      constant := (7907810486092818555354842386275680501317027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208775072247503846357/50000000000000000000)
  centralHi := (83510028899001538543/20000000000000000000)
  directionLo := (105130517287330615701/25000000000000000000)
  directionHi := (84104413829864492561/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree072.table
  base := (-4993987725757314395475276084218478503/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-83703291641866282234291308520063189125000000000)
      constant := (1599442286429010034080008129668216795682373264965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree072.table
  base := (-199761073753220928438492823716157615987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-238448168796430454448960143864907000000000000)
      constant := (4557569337465144279870140022134070849457809533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105130517287330615701/25000000000000000000)
  centralHi := (84104413829864492561/20000000000000000000)
  directionLo := (423473137418955162559/100000000000000000000)
  directionHi := (1323353554434234883/312500000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree073.table
  base := (356310529218547350504356143583101029397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-678917399907960531188458678166390141750000000000)
      constant := (13161031316581312028486358409702121015784397988093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree073.table
  base := (178154597708278569503272670173534648499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1087904873251443777115595427037411500000000000)
      constant := (21094878411774689852665832411522707593467751131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423473137418955162559/100000000000000000000)
  centralHi := (1323353554434234883/312500000000000000)
  directionLo := (213201891167315295417/50000000000000000000)
  directionHi := (85280756466926118167/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree074.table
  base := (934081233066727359277743905042309550761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-688208466680990804502586888172274770500000000000)
      constant := (13531759404448128199204497228316626318170339838609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree074.table
  base := (46704004815471890727592394696517283597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-551396493459475254605435103341370750000000000)
      constant := (10844542730938765458460202796995246963197561465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213201891167315295417/50000000000000000000)
  centralHi := (85280756466926118167/20000000000000000000)
  directionLo := (85862884429328313397/20000000000000000000)
  directionHi := (214657211073320783493/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree075.table
  base := (1533550823870477734666002562267964262373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-697499533454021077816715098178159399250000000000)
      constant := (13907722529846632414821173797597983107592724521037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree075.table
  base := (9584686595104815433889787153938016279/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-31046697238512701147392916286890875000000000)
      constant := (619213420240721626860858390289081905801248780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85862884429328313397/20000000000000000000)
  centralHi := (214657211073320783493/50000000000000000000)
  directionLo := (432205461021642463937/100000000000000000000)
  directionHi := (216102730510821231969/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree076.table
  base := (1077358903180549770938891229985442516247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-353395300113525675565421654092022014000000000000)
      constant := (7144460335801783599004811313344602424757342765743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree076.table
  base := (2154716981091932925704124686728771127087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2265138428507927946802839531946803000000000000)
      constant := (45805342756632771404164864438583545617264810103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432205461021642463937/100000000000000000000)
  centralHi := (216102730510821231969/50000000000000000000)
  directionLo := (435077289697768806961/100000000000000000000)
  directionHi := (217538644848884403481/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree077.table
  base := (699395230869771552133276340898934841427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-179020416750020406111242879547482164187500000000)
      constant := (3668838452979689373162083122893166598987485146163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree077.table
  base := (139879011024322919781351543404764005667/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-573728663960735352748347272809365750000000000)
      constant := (11761025091197450288673912710133498940865530615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435077289697768806961/100000000000000000000)
  centralHi := (217538644848884403481/50000000000000000000)
  directionLo := (437930286101089362979/100000000000000000000)
  directionHi := (21896514305054468149/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree078.table
  base := (138485564736442025859938856013792390263/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-725372733773111897759099728195813285500000000000)
      constant := (15067021935827547136106915139488073564207200861175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree078.table
  base := (865534629918637975732323919719005282019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-64574746754943190977331629181336750000000000)
      constant := (1341656639833237799813781728059750005626657779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437930286101089362979/100000000000000000000)
  centralHi := (21896514305054468149/5000000000000000000)
  directionLo := (88152963185228827187/20000000000000000000)
  directionHi := (1721737562211500531/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree079.table
  base := (2074195751339968831598041967534000539121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-367331900273071085536613969100848957125000000000)
      constant := (7731962515374475437118070712217034833462075721449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree079.table
  base := (1037097748204620599361196160514252418461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-588616777628242084843622052454695750000000000)
      constant := (12392989681015869574987837798086727867973157109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88152963185228827187/20000000000000000000)
  centralHi := (1721737562211500531/390625000000000000)
  directionLo := (221790616591546464469/50000000000000000000)
  directionHi := (443581233183092928939/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree080.table
  base := (151760541541332462636316090650750866079/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-92994358414896555548419518525947817875000000000)
      constant := (1983257885763230606819788346299477848337300029404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree080.table
  base := (1214084223802675095968636475909696993441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-596060834461995450891259442277360750000000000)
      constant := (12715264850300979215402264910114407042895424729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221790616591546464469/50000000000000000000)
  centralHi := (443581233183092928939/100000000000000000000)
  directionLo := (446379880713792031701/100000000000000000000)
  directionHi := (223189940356896015851/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree081.table
  base := (5585975970343389431860876845444832869253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-753245934092202717701484358213467171750000000000)
      constant := (16273436093005702918513185998119453822894439883757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree081.table
  base := (174561737524454879193161494580147773139/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-33528049516430489829938712894445875000000000)
      constant := (724540847736302332066082475360021224697574796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446379880713792031701/100000000000000000000)
  centralHi := (223189940356896015851/50000000000000000000)
  directionLo := (17966443627157153929/4000000000000000000)
  directionHi := (224580545339464424113/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree082.table
  base := (792163362220115335654352665123634619097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-95317125108154123876951571027418975062500000000)
      constant := (2085755505496527637315325100532053213104570397393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree082.table
  base := (6337306583198882705445760643802268792107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2443795792518008731946136887690763000000000000)
      constant := (53489603607613731252364699838898111132829102483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17966443627157153929/4000000000000000000)
  centralHi := (224580545339464424113/50000000000000000000)
  directionLo := (112981296254543467329/25000000000000000000)
  directionHi := (451925185018173869317/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree083.table
  base := (3555164833838116492287363715226741370927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-385914033819131632164870389112618214625000000000)
      constant := (8551943466359857228321546808123420216744899256663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree083.table
  base := (7110329399966407932092208716282607508073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2473572019853022196136686446981423000000000000)
      constant := (54829047092928329627549321688958464620033763937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112981296254543467329/25000000000000000000)
  centralHi := (451925185018173869317/100000000000000000000)
  directionLo := (90934495177030905107/20000000000000000000)
  directionHi := (14208514871411078923/3125000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree084.table
  base := (7905043906879279715618754729039747844021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-781119134411293537643868988231121058000000000000)
      constant := (17526964753963465745279852963141318876063722999549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree084.table
  base := (7905043679075283523333040138863336839127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-278149805243115073369692889585787000000000000)
      constant := (6242807941786649803023007440359798081006039207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90934495177030905107/20000000000000000000)
  centralHi := (14208514871411078923/3125000000000000000)
  directionLo := (28587704128682158857/6250000000000000000)
  directionHi := (457403266058914541713/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree085.table
  base := (8721449301589824411622461496763362823679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-790410201184323810957997198237005686750000000000)
      constant := (17955277503260293758883476670374229701568174341751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree085.table
  base := (8721449107769748942863116706975038996121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2533124474523049124517785565562743000000000000)
      constant := (57558276742878870951566307846534155544215013649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/6250000000000000000)
  centralHi := (457403266058914541713/100000000000000000000)
  directionLo := (115029462333348511471/25000000000000000000)
  directionHi := (92023569866678809177/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree086.table
  base := (4779772793996090158502341206062737052553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-399850633978677042136062704121445157750000000000)
      constant := (9194412588437261894071936871888104905032337361457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree086.table
  base := (2389886355777104582889512879331709722189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-640725175464515647177083781213350750000000000)
      constant := (14737015720349002516396107507357744838385992741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115029462333348511471/25000000000000000000)
  centralHi := (92023569866678809177/20000000000000000000)
  directionLo := (18512660435453944497/4000000000000000000)
  directionHi := (231408255443174306213/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree087.table
  base := (10419332544277925154186707494118810017701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-808992334730384357586253618248774944250000000000)
      constant := (18827607771665311087987164739214209444468601651469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree087.table
  base := (10419332404028851418910520668994763227979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-288075214354786228099876076016007000000000000)
      constant := (6706069986844653746292087414874181601432242139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18512660435453944497/4000000000000000000)
  centralHi := (231408255443174306213/50000000000000000000)
  directionLo := (465499527629018527793/100000000000000000000)
  directionHi := (232749763814509263897/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree088.table
  base := (1130080998395623514711813510477996133329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-409141700751707315450190914127329786500000000000)
      constant := (9635812642495957038397628908488394957146425863005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree088.table
  base := (1412601233084573873267524739942789002221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-327806644566011189636179280429340375000000000)
      constant := (7722247216883057629392566667318877394241764549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465499527629018527793/100000000000000000000)
  centralHi := (232749763814509263897/50000000000000000000)
  directionLo := (468167168537761865729/100000000000000000000)
  directionHi := (46816716853776186573/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree089.table
  base := (12203977750229825771311746637725096745407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-827574468276444904214510038260544201750000000000)
      constant := (19720877714634056706960329323257611689370375593783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree089.table
  base := (3050994412199275763280086689781887650813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-663057345965775745319995950681345750000000000)
      constant := (15804526608673657517243824983691528710829734997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468167168537761865729/100000000000000000000)
  centralHi := (46816716853776186573/10000000000000000000)
  directionLo := (58852461871096945191/12500000000000000000)
  directionHi := (470819694968775561529/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree090.table
  base := (13128835711266695515939551796131265827409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-836865535049475177528638248266428830500000000000)
      constant := (20175365058724975557480799585523301628581286272121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree090.table
  base := (13128835625021203185904906598985481148767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-298000623466457382830059262446227000000000000)
      constant := (7186112886059144698838820855517915810470934447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58852461871096945191/12500000000000000000)
  centralHi := (470819694968775561529/100000000000000000000)
  directionLo := (473457360956946791293/100000000000000000000)
  directionHi := (236728680478473395647/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree091.table
  base := (879711484764058765714946536352086567169/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-105769575227813181355345807284039182406250000000)
      constant := (2579385914461891316700033379848799553225181095622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree091.table
  base := (219927870045337013603863953745498023847/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-338972729816641238707635365163337875000000000)
      constant := (8268588293695824140216511368202478873751316344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473457360956946791293/100000000000000000000)
  centralHi := (236728680478473395647/50000000000000000000)
  directionLo := (119020103374950470983/25000000000000000000)
  directionHi := (476080413499801883933/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree092.table
  base := (15043621791910658401570054813379382377787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-855447668595535724156894668278198088000000000000)
      constant := (21100044484224880239229800240658570175960085766003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree092.table
  base := (15043621729580643376648734450965203920829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2741558065868143373851632480597363000000000000)
      constant := (67639177555584648074208337102544916336684090901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119020103374950470983/25000000000000000000)
  centralHi := (476080413499801883933/100000000000000000000)
  directionLo := (239344546413725543619/50000000000000000000)
  directionHi := (478689092827451087239/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree093.table
  base := (8016774869984045290571466273830533512087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-432369367684282998735511439142041358375000000000)
      constant := (10785118281602346939675890949462387205942096712703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree093.table
  base := (16033549686989319452566922518989404585471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-307926032578128537560242448876447000000000000)
      constant := (7682936621004949980010219664949966588515359311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/50000000000000000000)
  centralHi := (478689092827451087239/100000000000000000000)
  directionLo := (60160454082420525723/12500000000000000000)
  directionHi := (96256726531872841157/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree094.table
  base := (8522583767258605506288638879218454355429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-437014901070798135392575544144983672750000000000)
      constant := (11022831775850849577615657861057878331732285707501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree094.table
  base := (17045167489491829994356675139527400872543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2801110520538170302232731599178683000000000000)
      constant := (70670462446968469241639584724746140650186403367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60160454082420525723/12500000000000000000)
  centralHi := (96256726531872841157/20000000000000000000)
  directionLo := (483864260448753916871/100000000000000000000)
  directionHi := (60483032556094239609/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree095.table
  base := (18078475120167498628848224572580571431139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-883320868914626544099279298295851974250000000000)
      constant := (22526325448931556927561269282265715454495562602491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree095.table
  base := (18078475081905753461195827722049236214239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2830886747873183766423281158469343000000000000)
      constant := (72211276126852835055965599537826486797803809191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483864260448753916871/100000000000000000000)
  centralHi := (60483032556094239609/12500000000000000000)
  directionLo := (3800243731369453063/781250000000000000)
  directionHi := (97286239523057998413/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree096.table
  base := (19133472450347972295716462967688700928031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-892611935687656817413407508301736603000000000000)
      constant := (23012222254234814232985002263014025502531375797239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree096.table
  base := (19133472417837372607372083477112489104797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-317851441689799692290425635306667000000000000)
      constant := (8196541180732534522816588914527836057577281677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3800243731369453063/781250000000000000)
  centralHi := (97286239523057998413/20000000000000000000)
  directionLo := (48898465976681829247/10000000000000000000)
  directionHi := (488984659766818292471/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree097.table
  base := (10105079742951560353383137803851492607567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-450951501230343545363767859153810615875000000000)
      constant := (11751676983528511207061128661312935657994930648823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree097.table
  base := (4042031891656429824464734869129685346147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2890439202543210694804380277050663000000000000)
      constant := (75343245944418799291178809948446364472346716215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/10000000000000000000)
  centralHi := (488984659766818292471/100000000000000000000)
  directionLo := (245762428455356446571/50000000000000000000)
  directionHi := (491524856910712893143/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree098.table
  base := (4261707238782476401529911668308346088937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-911194069233717364041663928313505860500000000000)
      constant := (23999720586932020751540511921492334577180434751765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree098.table
  base := (21308536170448082308383575731992602732519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-2920215429878224158994929836341323000000000000)
      constant := (76934402078843060533801673452033306393371654511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245762428455356446571/50000000000000000000)
  centralHi := (491524856910712893143/100000000000000000000)
  directionLo := (494051993655447689653/100000000000000000000)
  directionHi := (247025996827723844827/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree099.table
  base := (2242860254669757377384375033932881578553/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-460242568003373818677896069159695244625000000000)
      constant := (12250661056733940752247848426974794583034767527285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree099.table
  base := (700893828961451538183391381428332660647/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-40972106350183855877576102717110875000000000)
      constant := (1090865819841872625583137843929663774769286108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494051993655447689653/100000000000000000000)
  centralHi := (247025996827723844827/50000000000000000000)
  directionLo := (19862650776117401767/4000000000000000000)
  directionHi := (31035391837683440261/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree100.table
  base := (5892589630247086136585155004686246935993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-232444050694944477667480087081318779500000000000)
      constant := (6252039636583773140909714747100214260308143062817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree100.table
  base := (2946294813007510040982249647948598950711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-372470985568531385922003619365330375000000000)
      constant := (10020882099085322476387719336509567485794807359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19862650776117401767/4000000000000000000)
  centralHi := (31035391837683440261/6250000000000000000)
  directionLo := (249533939266071582347/50000000000000000000)
  directionHi := (99813575706428632939/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree101.table
  base := (3091725512152560640332825623090805337837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-117383408694101022998006069791394968343750000000)
      constant := (3190028735657077677538945102827998747208194326953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree101.table
  base := (618345102071101993690518487526651997073/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-376193013985408068945822314276662875000000000)
      constant := (10226069421270287825003375615486754997276024685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/50000000000000000000)
  centralHi := (99813575706428632939/20000000000000000000)
  directionLo := (125389252643617682661/25000000000000000000)
  directionHi := (100311402114894146129/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree102.table
  base := (12959469629472972629766596744035010655199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-474179168162919228649088384168522187750000000000)
      constant := (13018768064999780451674257918259892811810043568631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree102.table
  base := (259189392467378963828045442248587060749/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-84425564978285500437698002041776750000000000)
      constant := (2318523187786411894055014838389786684330892725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125389252643617682661/25000000000000000000)
  centralHi := (100311402114894146129/20000000000000000000)
  directionLo := (12600846259533163899/2500000000000000000)
  directionHi := (504033850381326555961/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree103.table
  base := (27125763992336770441268120791911012575137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-957649403098868730612304978342929004250000000000)
      constant := (26560077280368104839883321690773499141314127618153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree103.table
  base := (847680124436594137921646460053578833131/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-383637070819161434993459704099327875000000000)
      constant := (10642736870312925243248817573325670647321281356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12600846259533163899/2500000000000000000)
  centralHi := (504033850381326555961/100000000000000000000)
  directionLo := (126624644571083403003/25000000000000000000)
  directionHi := (506498578284333612013/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree104.table
  base := (14177139142884002833108559787831012154897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-483470234935949501963216594174406816500000000000)
      constant := (13543926668098820951237607660615217939054395697593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree104.table
  base := (28354278276967340441775398522556094463263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-3098872793888304944138227192085283000000000000)
      constant := (86833735976214828370901255851939599449703779047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126624644571083403003/25000000000000000000)
  centralHi := (506498578284333612013/100000000000000000000)
  directionLo := (508951370248550332407/100000000000000000000)
  directionHi := (63618921281068791551/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree105.table
  base := (296044821294669943355327255833300913283/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-244057884161232319310140349588674565437500000000)
      constant := (6905216074337447405526387857201069046039556245675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree105.table
  base := (29604482121995795242777579710004164927751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-347627669024813156480975194597327000000000000)
      constant := (9838039755667068650571702396653715995400792791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508951370248550332407/100000000000000000000)
  centralHi := (63618921281068791551/12500000000000000000)
  directionLo := (511392398019077620791/100000000000000000000)
  directionHi := (63924049752384702599/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree106.table
  base := (3859546939402312773598796262623409444191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-43855580429777480889760128531531812500000000)
      constant := (1253075389983455806927381991311573860914416831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree106.table
  base := (6175275101775300486362809317299868937269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-3158425248558331872519326310666603000000000000)
      constant := (90267760436498657677763955641262326769074786305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511392398019077620791/100000000000000000000)
  centralHi := (63924049752384702599/12500000000000000000)
  directionLo := (256910914630698613947/50000000000000000000)
  directionHi := (102764365852279445579/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree107.table
  base := (80424896090291948129619400352414646553/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-124351708773873727983602227295808439906250000000)
      constant := (3587823866896892891158668107790722615644732685350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree107.table
  base := (8042489607683446164875006487570042095183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-797050368973336334177468967489315750000000000)
      constant := (23002485970597001308273230072671382989816357527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256910914630698613947/50000000000000000000)
  centralHi := (102764365852279445579/20000000000000000000)
  directionLo := (258119913847883007819/50000000000000000000)
  directionHi := (516239827695766015639/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree108.table
  base := (8371307721589271935622178662786396668683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-251026184241005024295736507093088037000000000000)
      constant := (7312826652917091565525083842821983737323338287427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree108.table
  base := (33485230881788476891200732670091060865751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-357553078136484311211158381027547000000000000)
      constant := (10418767570934385064741763327948125037824250791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258119913847883007819/50000000000000000000)
  centralHi := (516239827695766015639/100000000000000000000)
  directionLo := (20745862129038838269/4000000000000000000)
  directionHi := (259323276612985478363/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree109.table
  base := (17411096430530206760277788242102697628281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-506697901868525185248537119189118388375000000000)
      constant := (14902628596559400313493538761895012852448139389489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree109.table
  base := (3482219285718330851720834050045335054709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1623876965281686132545487494269291500000000000)
      constant := (47772326602171334608110485127436992530485463105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20745862129038838269/4000000000000000000)
  centralHi := (259323276612985478363/50000000000000000000)
  directionLo := (104208432412546282321/20000000000000000000)
  directionHi := (260521081031365705803/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree110.table
  base := (4522605544515759858440821761448603944931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-127835858813760080476400306048015175687500000000)
      constant := (3795555334933547491802596075565637764271945903339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree110.table
  base := (9045211088209021821933713212468637740453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-819382539474596432320381136957310750000000000)
      constant := (24334294770000602788386897395837172125646612157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104208432412546282321/20000000000000000000)
  centralHi := (260521081031365705803/50000000000000000000)
  directionLo := (6542835085525227189/1250000000000000000)
  directionHi := (523426806842018175121/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree111.table
  base := (37561185368107815311555660760906505606967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1031977937283110917125330658390006034250000000000)
      constant := (30928863070668304440420696850063836021258162797423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree111.table
  base := (234757408533226615474794090549894974959/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-45934810906019433242667695932220875000000000)
      constant := (1377034524517125702184096377432923786375366380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6542835085525227189/1250000000000000000)
  centralHi := (523426806842018175121/100000000000000000000)
  directionLo := (525800636738542895373/100000000000000000000)
  directionHi := (262900318369271447687/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree112.table
  base := (38963215894109562245262611016950055630143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1041269004056141190439458868395890663000000000000)
      constant := (31498518366677565437352115620419171713282226374167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree112.table
  base := (19481607945870558774359690404241376287491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1668541306284206328831311833205281500000000000)
      constant := (50486286629951901002688461574858195000787179179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525800636738542895373/100000000000000000000)
  centralHi := (262900318369271447687/50000000000000000000)
  directionLo := (264081898787328324521/50000000000000000000)
  directionHi := (528163797574656649043/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree113.table
  base := (5048366991462231442583457787963331614327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-131320008853646432969198384800221911468750000000)
      constant := (4009176070932713075658339731152261946185545953763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree113.table
  base := (40386935929688547240337748113430597156483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-3366858839903426121853173225701223000000000000)
      constant := (102815441563904776459688081383694361762392477227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/50000000000000000000)
  centralHi := (528163797574656649043/100000000000000000000)
  directionLo := (530516431924882629107/100000000000000000000)
  directionHi := (132629107981220657277/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree114.table
  base := (41832345478828138176724216771909028728487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1059851137602201737067715288407659920500000000000)
      constant := (32653533672991770841138375154039946538452481034303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree114.table
  base := (10458086369280912041048661239410707680941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-94350974089956655167881188471996750000000000)
      constant := (2907641407698434793608791953065218877419623581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530516431924882629107/100000000000000000000)
  centralHi := (132629107981220657277/25000000000000000000)
  directionLo := (266429339608147494313/50000000000000000000)
  directionHi := (532858679216294988627/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree115.table
  base := (10824861133445714283006470362138277067131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-267285551093808002595460874603386137312500000000)
      constant := (8309723420810860783498871098176643620821039930139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree115.table
  base := (1082486113308426274765051543083992328203/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-428301411821681631279284043035317875000000000)
      constant := (13318940074942859744867949327666100114691209535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266429339608147494313/50000000000000000000)
  centralHi := (532858679216294988627/100000000000000000000)
  directionLo := (535190675824943819543/100000000000000000000)
  directionHi := (66898834478117977443/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree116.table
  base := (699816142111239689526652503885470469729/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-134804158893532785461996463552428647250000000000)
      constant := (4228686074774536632153333940768672887326351193608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree116.table
  base := (22394116546946525204101033575391795174913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1728093760954233257212410951786601500000000000)
      constant := (54222365665518658056249168166655684355290627897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535190675824943819543/100000000000000000000)
  centralHi := (66898834478117977443/12500000000000000000)
  directionLo := (268756277584257483033/50000000000000000000)
  directionHi := (537512555168514966067/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree117.table
  base := (23149355580813011453141455249491002526019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-543862168960646278505049959212656903375000000000)
      constant := (17212659208916582328053342938917721854486137187211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree117.table
  base := (46298711160585997192328645917151758530667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-387329305471497775401707940318207000000000000)
      constant := (12261635874619140881211873666346351014753092347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/50000000000000000000)
  centralHi := (537512555168514966067/100000000000000000000)
  directionLo := (539824447795402820437/100000000000000000000)
  directionHi := (269912223897701410219/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree118.table
  base := (47830878732285623467523924068588952477117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1097015404694322830324228128431198435500000000000)
      constant := (35026383142139653045676525363185240447140195352773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree118.table
  base := (23915439365701816830165762480638284535089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1757869988289246721402960511077261500000000000)
      constant := (56140747610550904147682507187116575331072452841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539824447795402820437/100000000000000000000)
  centralHi := (269912223897701410219/50000000000000000000)
  directionLo := (542126481470364372243/100000000000000000000)
  directionHi := (135531620367591093061/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree119.table
  base := (9876947161248836364436288215953724258329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1106306471467353103638356338437083064250000000000)
      constant := (35632682771103666008140888845526405770425753988005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree119.table
  base := (49384735805496267109420452553249612124363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-3545516203913506906996470581445183000000000000)
      constant := (114225048379587387497639899533925128652470224947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542126481470364372243/100000000000000000000)
  centralHi := (135531620367591093061/25000000000000000000)
  directionLo := (272209390628456766089/50000000000000000000)
  directionHi := (544418781256913532179/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree120.table
  base := (3185017648924064267469275636145926906939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-139449692280047922119060568555370961625000000000)
      constant := (4530527163089381922445202542678998062327807025382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree120.table
  base := (50960282382150851820109869453585510249461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-397254714583168930131891126748427000000000000)
      constant := (12909486927444072818498242015450764557167532901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272209390628456766089/50000000000000000000)
  centralHi := (544418781256913532179/100000000000000000000)
  directionLo := (136675367399151520703/25000000000000000000)
  directionHi := (546701469596606082813/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree121.table
  base := (210230073845227583525462829346070743311/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-562444302506706825133306379224426160875000000000)
      constant := (18430493371482653559098676964578397117611953694875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree121.table
  base := (26278759230384599087582578408314450461503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1802534329291766917688784850013251500000000000)
      constant := (59081248561651236318576766383609934802987929607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/25000000000000000000)
  centralHi := (546701469596606082813/100000000000000000000)
  directionLo := (137243666596339370291/25000000000000000000)
  directionHi := (109794933277071496233/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree122.table
  base := (54176444041305517389634822587522975624639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1134179671786443923580740968454736950500000000000)
      constant := (37482991085847280714735168265542844555509018803991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree122.table
  base := (846506938138275810188899942933766846543/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-454355610739818412446014907414645375000000000)
      constant := (15019549088560259969336326225763192294486474936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137243666596339370291/25000000000000000000)
  centralHi := (109794933277071496233/20000000000000000000)
  directionLo := (55123848904692811301/10000000000000000000)
  directionHi := (551238489046928113011/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree123.table
  base := (11163411824471630445411376512292839025889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1143470738559474196894869178460621579250000000000)
      constant := (38110230333354990091157920146922943041083480576205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree123.table
  base := (3488566195123230665500457673329982234303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-50897515461855010607759289147330875000000000)
      constant := (1696764848646061083989904640612656755886242846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55123848904692811301/10000000000000000000)
  centralHi := (551238489046928113011/100000000000000000000)
  directionLo := (17296657893865732553/3125000000000000000)
  directionHi := (553493052603703441697/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree124.table
  base := (28739681852055288519007534964043585439493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-576380902666252235104498694233253104000000000000)
      constant := (19371352242741709692443164170329280891376660154317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree124.table
  base := (7184920462972871805401113356712031850371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-461799667573571778493652297237310375000000000)
      constant := (15524315788173680274501251078258844673019481899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17296657893865732553/3125000000000000000)
  centralHi := (553493052603703441697/100000000000000000000)
  directionLo := (111147693948977954547/20000000000000000000)
  directionHi := (8683413589763902699/1562500000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree125.table
  base := (11832671557253229550993063024561688100357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1162052872105534743523125598472390836750000000000)
      constant := (39380413542228368065791121406767442538733282901665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree125.table
  base := (2958167889299422887763779379223161962929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-931043391980896923034941984297285750000000000)
      constant := (31559691079271956570602344135992159425480629005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111147693948977954547/20000000000000000000)
  centralHi := (8683413589763902699/1562500000000000000)
  directionLo := (278987425446120019813/50000000000000000000)
  directionHi := (557974850892240039627/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree126.table
  base := (60869041368576603462547172689855019974661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1171343938878565016837253808478275465500000000000)
      constant := (40023357503586320717354700741680557829620825477709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree126.table
  base := (1902157542760663640904994260314298910349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-52138191600813904949032187451108375000000000)
      constant := (1781941432466671507159462942274442773228277236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278987425446120019813/50000000000000000000)
  centralHi := (557974850892240039627/100000000000000000000)
  directionLo := (1400505760658545197/250000000000000000)
  directionHi := (560202304263418078801/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree127.table
  base := (6259641445083433482519203243462694710777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-590317502825797645075691009242080047125000000000)
      constant := (20335768184777168778149718556973624651707073456565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree127.table
  base := (15649103612658713230559411622408296929317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-945931505648403655130216763942615750000000000)
      constant := (32594395691729410528028307523027674773386182973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1400505760658545197/250000000000000000)
  centralHi := (560202304263418078801/100000000000000000000)
  directionLo := (112484187186620855349/20000000000000000000)
  directionHi := (281210467966552138373/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree128.table
  base := (4021592314554117747891887861674776615411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-148740759053078195433188778561255590375000000000)
      constant := (5165618767516245298722234122874288372822935528918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree128.table
  base := (32172738516348413181029523533936624589469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1906751124964314042355708307530561500000000000)
      constant := (66236081602515940899232112216397282720999619061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112484187186620855349/20000000000000000000)
  centralHi := (281210467966552138373/50000000000000000000)
  directionLo := (282315424945970108373/50000000000000000000)
  directionHi := (564630849891940216747/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree129.table
  base := (66116229114526479786786143990333115648521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1199217139197655836779638438495929351750000000000)
      constant := (41983598815311145234561915648188601475918664460049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree129.table
  base := (33058114557191607489634667891437534765989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-213515470959091197161220343019543500000000000)
      constant := (7476862469552029837598889782520213112755350549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315424945970108373/50000000000000000000)
  centralHi := (564630849891940216747/100000000000000000000)
  directionLo := (56683214810340500439/10000000000000000000)
  directionHi := (566832148103405004391/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree130.table
  base := (271634682782781775628161226092248024659/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-604254102985343055046883324250906990250000000000)
      constant := (21323741197548088632200186723256893194651575921375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree130.table
  base := (8488583836946755500619082697458760782917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3507929437144838425103460248291250000000000)
      linear := (-484131838074831876636564466705305375000000000)
      constant := (17088958313453270601471207725413205267960161373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56683214810340500439/10000000000000000000)
  centralHi := (566832148103405004391/100000000000000000000)
  directionLo := (71128116319838911237/12500000000000000000)
  directionHi := (569024930558711289897/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree131.table
  base := (278891207105089314581235354431634932903/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-608899636371858191703947429253849304625000000000)
      constant := (21658300439741818061572189191497515700264548825875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree131.table
  base := (17430700444042365679169504627187505203623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-975707732983417119320766323233275750000000000)
      constant := (34714147343024058719001797319424185673583171887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71128116319838911237/12500000000000000000)
  centralHi := (569024930558711289897/100000000000000000000)
  directionLo := (35700580958112788287/6250000000000000000)
  directionHi := (571209295329804612593/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree132.table
  base := (8944827794521708812954814391797131181957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-153386292439593332090252883564197904750000000000)
      constant := (5498869283559042494194697704496583246611055870733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree132.table
  base := (14311724471217302810060725778787389827703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-436956351029853549052623872469307000000000000)
      constant := (15668699227260331510049950021905180160607254115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35700580958112788287/6250000000000000000)
  centralHi := (571209295329804612593/100000000000000000000)
  directionLo := (286692669310272775609/50000000000000000000)
  directionHi := (573385338620545551219/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree133.table
  base := (14683226487066052235345535517273374440341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1236381406289776930036151278519467866750000000000)
      constant := (44670542562061308754340708124878423715104107388145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree133.table
  base := (73416132435256419303230294589028144194761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-3962383386603695405664164411514423000000000000)
      constant := (143196777527363290534138521540960206873972111809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286692669310272775609/50000000000000000000)
  centralHi := (573385338620545551219/100000000000000000000)
  directionLo := (143888288704037564231/25000000000000000000)
  directionHi := (23022126192646010277/4000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree134.table
  base := (37647666006842426847111596744385126089953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-622836236531403601675139744262676247750000000000)
      constant := (22677682880124865949359409752092693886035668682057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree134.table
  base := (37647666006811147952493232329139749642941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-1996079806969354434927356985402541500000000000)
      constant := (72696021409077287500867189757366862301550590229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143888288704037564231/25000000000000000000)
  centralHi := (23022126192646010277/4000000000000000000)
  directionLo := (577712836530961258967/100000000000000000000)
  directionHi := (72214104566370157371/12500000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree135.table
  base := (7719622109119023441934834379097746770807/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-627481769917918738332203849265618562125000000000)
      constant := (23022711931518470416808026408435702465863688181915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree135.table
  base := (38598110545568619644422426235347093747829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-223440880070762351891403529449763500000000000)
      constant := (8200227162095261609997181880628082199582805989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577712836530961258967/100000000000000000000)
  centralHi := (72214104566370157371/12500000000000000000)
  directionLo := (289932237327308476111/50000000000000000000)
  directionHi := (579864474654616952223/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree136.table
  base := (79118799667807602652561463782843256613277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1264254606608867749978535908537121753000000000000)
      constant := (46740716870422386134569579868099482267154369963813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree136.table
  base := (79118799667762710877361668176151293644621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4051712068608735798235813089386403000000000000)
      constant := (149832915826041944012063157248965336041362810149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289932237327308476111/50000000000000000000)
  centralHi := (579864474654616952223/100000000000000000000)
  directionLo := (116401631679336977551/20000000000000000000)
  directionHi := (145502039599171221939/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree137.table
  base := (40531533871752604430020255244433262855997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-636772836690949011646332059271503190875000000000)
      constant := (23720622391202809111407404656705630719594371433493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree137.table
  base := (81063067743467183426190581693856694226029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4081488295943749262426362648677063000000000000)
      constant := (152078523543134849738527281058277745360340709701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116401631679336977551/20000000000000000000)
  centralHi := (145502039599171221939/25000000000000000000)
  directionLo := (146035993832455220211/25000000000000000000)
  directionHi := (116828795065964176169/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree138.table
  base := (20757256329564302585611788243269040275849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-320709185038732074151698082137222752625000000000)
      constant := (12036751899746567790340423549643865823969140958481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree138.table
  base := (16605805063645000546494390663206004545207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-456807169253195858512990245329747000000000000)
      constant := (17148990229888029139312456253926713344561942435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146035993832455220211/25000000000000000000)
  centralHi := (116828795065964176169/20000000000000000000)
  directionLo := (586272011431513013773/100000000000000000000)
  directionHi := (293136005715756506887/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree139.table
  base := (10627084049005338714306724375520074756103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-161515975865994821240115067319346954906250000000)
      constant := (6107250665020506129962792205074119123607997573907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree139.table
  base := (8501667239201543124046009725473144808921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2070520375306888095403730883629191500000000000)
      constant := (78310040701806620357875503455820159034179684245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586272011431513013773/100000000000000000000)
  centralHi := (293136005715756506887/50000000000000000000)
  directionLo := (117678470224893366591/20000000000000000000)
  directionHi := (147098087781116708239/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree140.table
  base := (17405201792968989415471239109534873491323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1301418873700988843235048748560660268000000000000)
      constant := (49574237945938714534838664705399247854528768567935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree140.table
  base := (43513004482410922282257105507453710432903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2085408488974394827499005663274521500000000000)
      constant := (79458015773498515446295922684389677388630376207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117678470224893366591/20000000000000000000)
  centralHi := (147098087781116708239/25000000000000000000)
  directionLo := (147626269328921352967/25000000000000000000)
  directionHi := (590505077315685411869/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree141.table
  base := (17811407007330124280351767559546774528167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1310709940474019116549176958566544896750000000000)
      constant := (50295705476310079301946560907180695969470262401115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree141.table
  base := (17811407007326211312703616276272471544833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-466732578364867013243173431759967000000000000)
      constant := (17914306944349226060255368908821924645287515765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147626269328921352967/25000000000000000000)
  centralHi := (590505077315685411869/100000000000000000000)
  directionLo := (592610271434295463671/100000000000000000000)
  directionHi := (74076283929286932959/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree142.table
  base := (91109750607449320534404625851303902007393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1737534226267248762126671487130000000000000)
      linear := (-261853006793701525463857403009805500000000000)
      constant := (10121485401959531026220244369668936941988766937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree142.table
  base := (2847179706482273515008113601816530966803/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (198)
      previous := (99)
      next := (99)
      square := (695879674101336723884836391250000000000)
      linear := (-104899063494812948407535966205375000000000)
      constant := (4055700115553729014447790041638645114804908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592610271434295463671/100000000000000000000)
  centralHi := (74076283929286932959/12500000000000000000)
  directionLo := (594708013468168331921/100000000000000000000)
  directionHi := (297354006734084165961/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree143.table
  base := (1863683113544660850402072349487993910697/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-664646037010039831588716689289157077125000000000)
      constant := (25877172625421175514744958788613515787243041944825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree143.table
  base := (93184155677219012921208699256496518563463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4260145659953830047569660004421023000000000000)
      constant := (165904566829719919054683244791724809550705752847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594708013468168331921/100000000000000000000)
  centralHi := (297354006734084165961/50000000000000000000)
  directionLo := (596798381999382456531/100000000000000000000)
  directionHi := (149199595499845614133/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree144.table
  base := (95280250245995793685095926093847282965181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1338583140793109936491561588584198783000000000000)
      constant := (52491517495003059809454187177061483033977784075589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree144.table
  base := (47640125122991957097391820311118126232549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-238328993738269083986678309095093500000000000)
      constant := (9348202233786120659468514281140850474338279509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596798381999382456531/100000000000000000000)
  centralHi := (149199595499845614133/25000000000000000000)
  directionLo := (598881454238571797633/100000000000000000000)
  directionHi := (299440727119285898817/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree145.table
  base := (6087377144608328202815816743153592053963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-168484275945767526225711224823760426468750000000)
      constant := (6654240580470007628964052348076372638668479211994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree145.table
  base := (48699017156861596416125079685287680549543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2159849057311928487975379561501171500000000000)
      constant := (85323747197670674356293753574812809278852216367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598881454238571797633/100000000000000000000)
  centralHi := (299440727119285898817/50000000000000000000)
  directionLo := (300478653029101347757/50000000000000000000)
  directionHi := (120191461211640539103/20000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree146.table
  base := (49768753940221240074531974455234323335031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-678582637169585241559909004297984020250000000000)
      constant := (26990783348556656567723843852757691548040307580239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree146.table
  base := (99537507880433964054346365574463390267947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4349474341958870440141308682293003000000000000)
      constant := (173044129391293318701595662374895387553066487443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300478653029101347757/50000000000000000000)
  centralHi := (120191461211640539103/20000000000000000000)
  directionLo := (603026012024819743797/100000000000000000000)
  directionHi := (301513006012409871899/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree147.table
  base := (10169867094612169550904500435993300242003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-683228170556100378216973109300926334625000000000)
      constant := (27367221827531395423171542288084968970585798142535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree147.table
  base := (4067946837844579423080503712937317286233/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-486583396588209322703539804620407000000000000)
      constant := (19495282799556222532419135525663124410997513825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603026012024819743797/100000000000000000000)
  centralHi := (301513006012409871899/50000000000000000000)
  directionLo := (75635955678787431189/12500000000000000000)
  directionHi := (605087645430299449513/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree148.table
  base := (20776304702154012668279857996505085450113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1375747407885231029748074428607737298000000000000)
      constant := (55492555517608482355049933438021502727540205745485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree148.table
  base := (103881523510763959520355621660373685167491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4409026796628897368522407800874323000000000000)
      constant := (177887741809479364784104303744294177722363899179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75635955678787431189/12500000000000000000)
  centralHi := (605087645430299449513/100000000000000000000)
  directionLo := (121428455664429748413/20000000000000000000)
  directionHi := (303571139161074371033/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree149.table
  base := (53043032787193766752957602941790094604567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-692519237329130651531101319306810963375000000000)
      constant := (28127951142375193475787182170400614246114938141823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree149.table
  base := (106086065574382366337507540215110119644171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4438803023963910832712957360164983000000000000)
      constant := (180334719231713403791770064121235568018136394099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121428455664429748413/20000000000000000000)
  centralHi := (303571139161074371033/50000000000000000000)
  directionLo := (304594990766441884033/50000000000000000000)
  directionHi := (609189981532883768067/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree150.table
  base := (108312297136974699700728259175522398406981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1394329541431291576376330848619506555500000000000)
      constant := (57024483956488513042782311050121756794259431739789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree150.table
  base := (108312297136970325649085734192451295703471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-496508805699880477433722991050627000000000000)
      constant := (20310941940300905325148587892648196981641197311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304594990766441884033/50000000000000000000)
  centralHi := (609189981532883768067/100000000000000000000)
  directionLo := (611230824708522865587/100000000000000000000)
  directionHi := (152807706177130716397/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree151.table
  base := (5528010909926634109550171668789220184287/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-350905152051080462422614764656347796062500000000)
      constant := (14449575133205719122954458636368036034823340947515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree151.table
  base := (110560218198528979683729601533768411594591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4498355478633937761094056478746303000000000000)
      constant := (185279016502463649009577125327290862065634999079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611230824708522865587/100000000000000000000)
  centralHi := (152807706177130716397/25000000000000000000)
  directionLo := (306632438168113072541/50000000000000000000)
  directionHi := (613264876336226145083/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree152.table
  base := (22565965751812605927499549482748276671323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1412911674977352123004587268631275813000000000000)
      constant := (58577352013753499227978977882828542116623455667935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree152.table
  base := (112829828759059895710239554784757006798393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4528131705968951225284606038036963000000000000)
      constant := (187776336350979978146907772918392496641436292017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306632438168113072541/50000000000000000000)
  centralHi := (613264876336226145083/100000000000000000000)
  directionLo := (615292203771112710577/100000000000000000000)
  directionHi := (307646101885556355289/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree153.table
  base := (115121128818567636970073585764368498373809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1422202741750382396318715478637160441750000000000)
      constant := (59361638399280408083792835573099575276163423113721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree153.table
  base := (28780282204641246105705918722757830393157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (779539874921075205578546721842500000000000)
      linear := (-126608553702887908040976544370211750000000000)
      constant := (5285845472451589500683743339765562473011904437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615292203771112710577/100000000000000000000)
  centralHi := (307646101885556355289/50000000000000000000)
  directionLo := (617312873262285229773/100000000000000000000)
  directionHi := (308656436631142614887/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree154.table
  base := (58717059188524338368996932414595450370307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-715746904261706334816421844321522535250000000000)
      constant := (30075579844701816911462065668981855814015284701883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree154.table
  base := (117434118377046431725229162032640217919563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4587684160638978153665705156618283000000000000)
      constant := (192821318474295479814965193991762756046792653747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617312873262285229773/100000000000000000000)
  centralHi := (308656436631142614887/50000000000000000000)
  directionLo := (154831737494522575391/25000000000000000000)
  directionHi := (123865389995618060313/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree155.table
  base := (59884398717254270889052595159920645196823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-720392437648221471473485949324464849625000000000)
      constant := (30472957942061605164173501270687017734626833193087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree155.table
  base := (29942199358626660441674502026585807946937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-1154365096993497904464063678977235750000000000)
      constant := (48842245187273715147951508532341025270744584753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154831737494522575391/25000000000000000000)
  centralHi := (123865389995618060313/20000000000000000000)
  directionLo := (310667249015320935321/50000000000000000000)
  directionHi := (621334498030641870643/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree156.table
  base := (122125165990949797386136256573986578415349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1450075942069473216261100108654814328000000000000)
      constant := (61745906983439173925082502473301253326468094033981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree156.table
  base := (122125165990948189425013879858188915261631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-516359623923222786894089363911067000000000000)
      constant := (21992602648072831241640827535662862321833881871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310667249015320935321/50000000000000000000)
  centralHi := (621334498030641870643/100000000000000000000)
  directionLo := (311667790249816898957/50000000000000000000)
  directionHi := (124667116099926759583/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree157.table
  base := (62251612023187570732837448518881944542131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-729683504421251744787614159330349478375000000000)
      constant := (31275566493675781407950690280843259638315983830139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree157.table
  base := (12450322404637378071972099397984817756963/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2338506421322009273118676917245131500000000000)
      constant := (100257323862488732166625068316826076484078271735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667790249816898957/50000000000000000000)
  centralHi := (124667116099926759583/20000000000000000000)
  directionLo := (625330259455466609289/100000000000000000000)
  directionHi := (62533025945546660929/10000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree158.table
  base := (3172574290019684284316434958370585573329/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1094863754326650126235068870827791250000000000)
      linear := (-183582259451941720361169566083322948187500000000)
      constant := (7920199236982552076479555972294144944521658913005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree158.table
  base := (126902971600786219880573883118655676054533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4706789069979032010427903393780923000000000000)
      constant := (203112652426060937292353833959100203366918107677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625330259455466609289/100000000000000000000)
  centralHi := (62533025945546660929/10000000000000000000)
  directionLo := (627318595981712411053/100000000000000000000)
  directionHi := (313659297990856205527/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree159.table
  base := (4041387770443417386804357227404688062619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-65768473762396050026854963451071031250000000)
      constant := (2855877968537102881018382661214151595914962016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree159.table
  base := (1616555108177354774996451849642495083017/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (389769937460537602789273360921250000000000)
      linear := (-65785629129361742703034068792660875000000000)
      constant := (2857325526887583756835194483573923552134886970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627318595981712411053/100000000000000000000)
  centralHi := (313659297990856205527/50000000000000000000)
  directionLo := (629300650196940974683/100000000000000000000)
  directionHi := (157325162549235243671/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree160.table
  base := (65883767603292007420442013154954697240429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4379455017306600504940275483311165000000000000)
      linear := (-743620104580797154758806474339176421500000000000)
      constant := (32499110213333841065798801029952236265268308272501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree160.table
  base := (32941883801645797591780461590389300522843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7015858874289676850206920496582500000000000)
      linear := (-1191585381162264734702250628090560750000000000)
      constant := (52089751063628219139833369059428092175420864067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629300650196940974683/100000000000000000000)
  centralHi := (157325162549235243671/25000000000000000000)
  directionLo := (315638240637964527529/50000000000000000000)
  directionHi := (631276481275929055059/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree161.table
  base := (134232351257974295337082184199119196736783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1496531275934624582831741158684237471750000000000)
      constant := (65824386048966176932214150213970776357476158296327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree161.table
  base := (67116175628986798866311884346716340752157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2398058875992036201499776035826451500000000000)
      constant := (105503675690940804728629709044061350163584610933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638240637964527529/50000000000000000000)
  centralHi := (631276481275929055059/100000000000000000000)
  directionLo := (633246147470274111011/100000000000000000000)
  directionHi := (158311536867568527753/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree162.table
  base := (136718856808363161093674798423743424230311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1505822342707654856145869368690122100500000000000)
      constant := (66655786575861302303894672097279286355271148682559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree162.table
  base := (136718856808362570858736026425716477742223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3118159499684300822314186887370000000000000)
      linear := (-536210442146565096354455736771507000000000000)
      constant := (23741386590890262642773370121258090764298546143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633246147470274111011/100000000000000000000)
  centralHi := (158311536867568527753/25000000000000000000)
  directionLo := (635209706128432743839/100000000000000000000)
  directionHi := (3970060663302704649/625000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree163.table
  base := (34806762964438394300483937625163804158049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-378778352370171282364999394674001682312500000000)
      constant := (16873105501838275058208176574348725633305017175281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree163.table
  base := (139227051857753077830101224571146091504051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4855670206654099331380651190234223000000000000)
      constant := (216354388062905274201468365594135606025447289819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635209706128432743839/100000000000000000000)
  centralHi := (3970060663302704649/625000000000000000)
  directionLo := (637167213715203355463/100000000000000000000)
  directionHi := (79645901714400419433/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree164.table
  base := (141756936406148500151487230703440230760873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1524404476253715402774125788701891358000000000000)
      constant := (68334292343441612583420949774741754027847960267537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree164.table
  base := (141756936406148077670821546595821906002143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4885446433989112795571200749524883000000000000)
      constant := (219053077616560474954748013558234576053411225767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637167213715203355463/100000000000000000000)
  centralHi := (79645901714400419433/12500000000000000000)
  directionLo := (31955936291533587571/5000000000000000000)
  directionHi := (639118725830671751421/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree165.table
  base := (1443085104535508693083409837930139670773/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2189727508653300252470137741655582500000000000)
      linear := (-383423885756686419022063499676943996687500000000)
      constant := (17295349396031720244394720422779817230100391640925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree165.table
  base := (2886170209071010237854935108134194474867/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-273067925629118125542319461600863500000000000)
      constant := (12320474887721005527680577048719214358695113675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31955936291533587571/5000000000000000000)
  centralHi := (639118725830671751421/100000000000000000000)
  directionLo := (641064297228637672831/100000000000000000000)
  directionHi := (5008314822098731819/781250000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree166.table
  base := (29376354799992720003614464944263960759031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1542986609799775949402382208713660615500000000000)
      constant := (70033737729408946697092541908475192324817486181195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree166.table
  base := (29376354799992659531631674759555602086963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4944998888659139723952299868106203000000000000)
      constant := (224500799150158280180711035957909008555417121735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641064297228637672831/100000000000000000000)
  centralHi := (5008314822098731819/781250000000000000)
  directionLo := (643003981834539534057/100000000000000000000)
  directionHi := (321501990917269767029/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree167.table
  base := (149476727045389578066669672422340222865559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1552277676572806222716510418719545244250000000000)
      constant := (70891312779287850605179224270957516028563042219471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree167.table
  base := (5979069081815572891641240316386663871779/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28063435497158707400827681986330000000000000)
      linear := (-4974775115994153188142849427396863000000000000)
      constant := (227249831130101147997131364707118714829968536275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643003981834539534057/100000000000000000000)
  centralHi := (321501990917269767029/50000000000000000000)
  directionLo := (322468916381446983621/50000000000000000000)
  directionHi := (644937832762893967243/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree168.table
  base := (30418673917966331054900334413304510068133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1561568743345836496030638628725429873000000000000)
      constant := (71754122733763633084097306436480807974134823972385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree168.table
  base := (76046684794915719456850798182154371034517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1559079749842150411157093443685000000000000)
      linear := (-278030630184953702907411054815973500000000000)
      constant := (12778646884378157355045482094050748184385000197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell193.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322468916381446983621/50000000000000000000)
  centralHi := (644937832762893967243/100000000000000000000)
  directionLo := (646865902334266129761/100000000000000000000)
  directionHi := (323432951167133064881/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree169.table
  base := (154731701633292646034902184171027788112401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8758910034613201009880550966622330000000000000)
      linear := (-1570859810118866769344766838731314501750000000000)
      constant := (72622167592836333986132028343390495348531851655769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree169.table
  base := (77365850816646231510811998060611883681953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (14031717748579353700413840993165000000000000)
      linear := (-2517163785332090058261974272989091500000000000)
      constant := (116399118758137730548993110475844849050766525657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell193.Kernel169
