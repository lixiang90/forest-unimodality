import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell159.Parameters
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31833_60208.Batch150_199
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch000_049
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch050_099
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch100_149
import ForestUnimodality.BinomialMassData.Q23881_45156.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree000.table
  base := (8794176081774840685433502997/100000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78678641569003247846492143750000000000)
      linear := (-5867163814410027372972522625000000000)
      constant := (109927201022185508567918787462500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree000.table
  base := (8794176081774840685433502997/100000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78678641569003247846492143750000000000)
      linear := (-5867163814410027372972522625000000000)
      constant := (109927201022185508567918787462500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree001.table
  base := (489305929284179718243579838936792994489179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-10089364241861505485835593164143070250000000000)
      constant := (6931497564475315019729308608534248515037530811251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree001.table
  base := (244602031106085327759314029478868527539567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-45413241628185180657071907361278738000000000000)
      constant := (31185254277676820462221461178348164698235306161407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (311979165212320689/625000000000000000)
  directionHi := (49916666433971310241/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree002.table
  base := (287492990658867640516405599917498782763823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-19514088234421165988503850706475551500000000000)
      constant := (4081618173133187287962558155645314926573770766087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree002.table
  base := (287387845029529289726619909343422333368261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-175671204269024117779781608848819651000000000000)
      constant := (36721212262098825326836825881147289911820234964981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311979165212320689/625000000000000000)
  centralHi := (49916666433971310241/100000000000000000000)
  directionLo := (1764820666484401639/2500000000000000000)
  directionHi := (70592826659376065561/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree003.table
  base := (180572043742764854641571514615636381266873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-28938812226980826491172108248808032750000000000)
      constant := (2580408434009699768758605064755381332154543281537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree003.table
  base := (180488832008373883198810948882404206914117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-28946213920186430471713266997231314000000000000)
      constant := (2579242159506961886763020887123468703839865205773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/2500000000000000000)
  centralHi := (70592826659376065561/100000000000000000000)
  directionLo := (86458202408106278219/100000000000000000000)
  directionHi := (4322910120405313911/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree004.table
  base := (121863593630093585600504443303755743728427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-38363536219540486993840365791140514000000000000)
      constant := (1766878810404400091410475538463141137540216424163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree004.table
  base := (60901550488030780587571709316441290035757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-172680323147165815355528598550672000500000000000)
      constant := (7947195598698951668649868909096879998859016466397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86458202408106278219/100000000000000000000)
  centralHi := (4322910120405313911/5000000000000000000)
  directionLo := (311979165212320689/312500000000000000)
  directionHi := (99833332867942620481/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree005.table
  base := (43988193849317289213296532070784993488979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-23894130106050073748254311666736497625000000000)
      constant := (654902606032485225268431951098370534276436027451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree005.table
  base := (8793322491719840349930337503432017494893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-215102683653492693588347495613803088000000000000)
      constant := (5891521930638136398630634331265944314801368261265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311979165212320689/312500000000000000)
  centralHi := (99833332867942620481/100000000000000000000)
  directionLo := (1744016552445966677/1562500000000000000)
  directionHi := (111617059356541867329/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree006.table
  base := (67135717986134682429553587218728556266017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-57212984204659807999176880875805476500000000000)
      constant := (1042455784320260611580885032865122420696559676873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree006.table
  base := (67104374340206861697317966926991899317767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-57227787591071015960259198372652039000000000000)
      constant := (1042059471919496210419716828069291614970565422623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/1562500000000000000)
  centralHi := (111617059356541867329/100000000000000000000)
  directionLo := (61135181211971042321/50000000000000000000)
  directionHi := (122270362423942084643/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree007.table
  base := (53370568035368619827497884004388772213437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-66637708197219468501845138418137957750000000000)
      constant := (880279925034179370079057891377831141549459490853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree007.table
  base := (53346921681522717845689940391770091991883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-599894809332292900107970579480130526000000000000)
      constant := (7920086938891334513502334509692127578380489174043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61135181211971042321/50000000000000000000)
  centralHi := (122270362423942084643/100000000000000000000)
  directionLo := (26413417132330687193/20000000000000000000)
  directionHi := (66033542830826717983/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree008.table
  base := (43616514117648347918245976307805282370609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-76062432189779129004513395960470439000000000000)
      constant := (779884876320893893089297318137598804460544072921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree008.table
  base := (43597841416757519296335964755606480958291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-684739530344946656573608373606392701000000000000)
      constant := (7017342304433991656127700438018172268782142600611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26413417132330687193/20000000000000000000)
  centralHi := (66033542830826717983/50000000000000000000)
  directionLo := (1764820666484401639/1250000000000000000)
  directionHi := (141185653318752131121/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree009.table
  base := (7254175613422453082472595496121732477287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-85487156182338789507181653502802920250000000000)
      constant := (718576444499193875742587403707670786185550407515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree009.table
  base := (4531936583960031729870873625817306898109/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-10688670157744450181100641218509095500000000000)
      constant := (89808136038828714169510287874870198067714220421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/1250000000000000000)
  centralHi := (141185653318752131121/100000000000000000000)
  directionLo := (149749999301913930721/100000000000000000000)
  directionHi := (74874999650956965361/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree010.table
  base := (30471127088934287473221290749514241866683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-94911880174898450009849911045135401500000000000)
      constant := (684141019426299631143943987714481468832856749427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree010.table
  base := (609160428300997968816855667496238255291/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-427214486185127084752441980929458525500000000000)
      constant := (3078390710677512156422503848431315505816783440275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149749999301913930721/100000000000000000000)
  centralHi := (74874999650956965361/50000000000000000000)
  directionLo := (39462589783556068601/25000000000000000000)
  directionHi := (31570071826844854881/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree011.table
  base := (25733651777278608166730924372762846562229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-104336604167458110512518168587467882750000000000)
      constant := (669730610185586561015449925886116587734419156701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree011.table
  base := (6430557958895550449929805180770931210861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-234818423345726981492630438996294806500000000000)
      constant := (1506887493745292096186069767983429570254747559581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39462589783556068601/25000000000000000000)
  centralHi := (31570071826844854881/20000000000000000000)
  directionLo := (165554853346810521411/100000000000000000000)
  directionHi := (41388713336702630353/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree012.table
  base := (21772253913446942948214156642012380625979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-113761328160017771015186426129800364000000000000)
      constant := (671292601632787996194380628297483355881188430451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree012.table
  base := (21762165917977715906861962726895621885009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-113790934932840186937351061123493489000000000000)
      constant := (671338725695799634578781054578484744251826006521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165554853346810521411/100000000000000000000)
  centralHi := (41388713336702630353/25000000000000000000)
  directionLo := (172916404816212556439/100000000000000000000)
  directionHi := (4322910120405313911/2500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree013.table
  base := (18406364229868205111306022318355892414651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-123186052152577431517854683672132845250000000000)
      constant := (686270102422891129404954811486533962729463736019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree013.table
  base := (18397389000551899473163149008103745949281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-1108963135408215438901797344237703576000000000000)
      constant := (6177282222471910928168052495034275850698959496401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172916404816212556439/100000000000000000000)
  centralHi := (4322910120405313911/2500000000000000000)
  directionLo := (44994275081978939931/25000000000000000000)
  directionHi := (7199084013116630389/4000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree014.table
  base := (3878539458668707112966803720500722899613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-33152694036284273005130735303616331625000000000)
      constant := (178234512874661124394467848897558305154127614597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree014.table
  base := (7753074804322791489008102527835136721811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-596903928210434597683717569181982875500000000000)
      constant := (3208867427747876757659202692565483105570547714531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44994275081978939931/25000000000000000000)
  centralHi := (7199084013116630389/4000000000000000000)
  directionLo := (2918297870090618879/1562500000000000000)
  directionHi := (186771063685799608257/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree015.table
  base := (13008213867566826355680222064865604053549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-142035500137696752523191198756797807750000000000)
      constant := (750058554704074899558072604132884941115026389781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree015.table
  base := (13001066259656560527388512816188460435491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-142072508603724772425896992498914214000000000000)
      constant := (750252266809296035063267388128691011241366157979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2918297870090618879/1562500000000000000)
  centralHi := (186771063685799608257/100000000000000000000)
  directionLo := (193326417796961652673/100000000000000000000)
  directionHi := (96663208898480826337/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree016.table
  base := (2705640199488376356278516894550125947747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-37865056032564103256464864074782572250000000000)
      constant := (199174361004207361751979903307721999641382689243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree016.table
  base := (10816188582804607549254407533107984847313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-1363497298446176708298710726616490101000000000000)
      constant := (7172484044272897552740531051505166762186521483073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193326417796961652673/100000000000000000000)
  centralHi := (96663208898480826337/50000000000000000000)
  directionLo := (199666665735885240961/100000000000000000000)
  directionHi := (99833332867942620481/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree017.table
  base := (2226381547142811386937888496097934595991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-40221237030704018382131928460365692562500000000)
      constant := (213030757248153345395946477165308741381351157479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree017.table
  base := (8899855951549659991397196634311061271583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-1448342019458830464764348520742752276000000000000)
      constant := (7671792075641374496579860337191716430699731597743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199666665735885240961/100000000000000000000)
  centralHi := (99833332867942620481/50000000000000000000)
  directionLo := (8232467527439494239/4000000000000000000)
  directionHi := (25726461023248419497/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree018.table
  base := (3607795157596501725453050615505589688359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-85154836057687867015597985691897625750000000000)
      constant := (457873691659769188087058216424757341353695772671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree018.table
  base := (721055589427452392169545656741674726097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-85177041137304678957221461937167469500000000000)
      constant := (458050226825873923479214965334289868322811151965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8232467527439494239/4000000000000000000)
  centralHi := (25726461023248419497/12500000000000000000)
  directionLo := (5294461999453204917/2500000000000000000)
  directionHi := (211778479978128196681/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree019.table
  base := (2859415389123250640962543101588980424071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-89867198053967697266932114463063866375000000000)
      constant := (493545080043387724335196472097853836901130777999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree019.table
  base := (2857185594557520685513774428359142321249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-809015730742068988847812054497638313000000000000)
      constant := (4443748801801751591954712763312739773987943179729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5294461999453204917/2500000000000000000)
  centralHi := (211778479978128196681/100000000000000000000)
  directionLo := (27197713073013718107/12500000000000000000)
  directionHi := (217581704584109744857/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree020.table
  base := (4387239108677476421929230232979980646273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-189159120100495055036532486468460214000000000000)
      constant := (1065754754639084970218902266164083695192954900137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree020.table
  base := (876659537731952565308815038778201985869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-1702876182496791734161261903121538801000000000000)
      constant := (9596003746714268841698292424668780108621829333745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27197713073013718107/12500000000000000000)
  centralHi := (217581704584109744857/100000000000000000000)
  directionLo := (1744016552445966677/781250000000000000)
  directionHi := (223234118713083734657/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree021.table
  base := (3197538346669718322715716568483444688227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-198583844093054715539200744010792695250000000000)
      constant := (1151411561291663190517509867271229145854634130363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree021.table
  base := (798515612051756541045425640191190904541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-49658913986373485850747213812438916000000000000)
      constant := (287984904797974968990937450277277598550813427429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/781250000000000000)
  centralHi := (223234118713083734657/100000000000000000000)
  directionLo := (114373451186767464487/50000000000000000000)
  directionHi := (9149876094941397159/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree022.table
  base := (2130305949826103286633333030857287392189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-208008568085614376041869001553125176500000000000)
      constant := (1243785553561757172893569680010037914698715519941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree022.table
  base := (1063623422037012309347137115968074960571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-936282812261049623546268745687031575500000000000)
      constant := (5599690671352064897061866365037665883917183268491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114373451186767464487/50000000000000000000)
  centralHi := (9149876094941397159/4000000000000000000)
  directionLo := (14633119932484264057/6250000000000000000)
  directionHi := (234129918919748224913/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree023.table
  base := (584647746684495929353516483709155891779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-108716646039087018272268629547728828875000000000)
      constant := (671323339664434877621783576497815814552280100651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree023.table
  base := (583304161166205508309690058737753686471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-978705172767376501779087642750162663000000000000)
      constant := (6044854040433904242123072803381205964239721362391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14633119932484264057/6250000000000000000)
  centralHi := (234129918919748224913/100000000000000000000)
  directionLo := (119695961211362762387/50000000000000000000)
  directionHi := (9575676896909020991/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree024.table
  base := (300896487466940401765229724502220678603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-226858016070733697047205516637790139000000000000)
      constant := (1447802211756814914151177937213979371684313163907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree024.table
  base := (149270097939084300436951205560305022889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-113458614808189264445767393312588194500000000000)
      constant := (724261262795434887406045932410610701815657108241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695961211362762387/50000000000000000000)
  centralHi := (9575676896909020991/4000000000000000000)
  directionLo := (61135181211971042321/25000000000000000000)
  directionHi := (48908144969576833857/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree025.table
  base := (-486304276274824407120726664757788321141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-236282740063293357549873774180122620250000000000)
      constant := (1559090537885890440647040774192402819986104667171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree025.table
  base := (-3906936413972567350523436522531135947/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2127099787560060516489450873752849676000000000000)
      constant := (14038911244922922993981681139088112761257068076625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61135181211971042321/25000000000000000000)
  centralHi := (48908144969576833857/20000000000000000000)
  directionLo := (124791666084928275601/50000000000000000000)
  directionHi := (249583332169856551203/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree026.table
  base := (-600941699082070777310788027892868128427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-122853732027926509026271015861227550750000000000)
      constant := (838188025718645941327554620111531134703634975837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree026.table
  base := (-1203686483127108006358844321632844580731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2211944508572714272955088667879111851000000000000)
      constant := (15095113619026594662901983545107635159075034068149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124791666084928275601/50000000000000000000)
  centralHi := (249583332169856551203/100000000000000000000)
  directionLo := (2036208449602573437/800000000000000000)
  directionHi := (127263028100160839813/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree027.table
  base := (-1853879746893283171028009718509376986919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-255132188048412678555210289264787582750000000000)
      constant := (1799544920671767857816477127796956107522703670689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree027.table
  base := (-1855453618744153521071450071734825771911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-255198803287263114380080718000597114000000000000)
      constant := (1800476199297417170777488843598863987509184787041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2036208449602573437/800000000000000000)
  centralHi := (127263028100160839813/50000000000000000000)
  directionLo := (259374607224318834659/100000000000000000000)
  directionHi := (12968730361215941733/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree028.table
  base := (-2449043325491793921967127225302836665547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-264556912040972339057878546807120064000000000000)
      constant := (1928501564405669501672816215989438976761458002557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree028.table
  base := (-2450415327537856428692506371945970859599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2381633950598021785886364256131636201000000000000)
      constant := (17365567937633682374107541153662865696831025989921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259374607224318834659/100000000000000000000)
  centralHi := (12968730361215941733/5000000000000000000)
  directionLo := (264134171323306871931/100000000000000000000)
  directionHi := (66033542830826717983/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree029.table
  base := (-1496521557313052152174584373932520312397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-136990818016765999780273402174726272625000000000)
      constant := (1031582854457351212880561763069332538651619434907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree029.table
  base := (-2994237684494791715026967009727997200481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2466478671610675542352002050257898376000000000000)
      constant := (18578237957682989003460871508918072597611959428399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264134171323306871931/100000000000000000000)
  centralHi := (66033542830826717983/25000000000000000000)
  directionLo := (8400296105302952563/3125000000000000000)
  directionHi := (268809475369694482017/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree030.table
  base := (-3490640978791823564536960563926048926627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-283406360026091660063215061891785026500000000000)
      constant := (2203469925392853703394938802834335822290443080037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree030.table
  base := (-3491679882338788594669620980601519918407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-283480376958147699868626649376017839000000000000)
      constant := (2204632148340579721889466149988020801298490669217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8400296105302952563/3125000000000000000)
  centralHi := (268809475369694482017/100000000000000000000)
  directionLo := (273404842013470460887/100000000000000000000)
  directionHi := (34175605251683807611/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree031.table
  base := (-246614834281615833852107091892715223931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-36603885502331415070735414929264688468750000000)
      constant := (293669695883491406251022946593896598955489328822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree031.table
  base := (-157869596491263362582599712635666449013/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2636168113635983055283277638510422726000000000000)
      constant := (21155412559699399458797930117691323818852858280675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273404842013470460887/100000000000000000000)
  centralHi := (34175605251683807611/12500000000000000000)
  directionLo := (138962118241169507353/50000000000000000000)
  directionHi := (277924236482339014707/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree032.table
  base := (-109049833819925443435545231685300332383/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-37781976001401372633568947122056248625000000000)
      constant := (312597629973107013806043263546491087138502736365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree032.table
  base := (-872555337980024113448652206886322118253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2721012834648636811748915432636684901000000000000)
      constant := (22518979566275498751433574773473853607769479085935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138962118241169507353/50000000000000000000)
  centralHi := (277924236482339014707/100000000000000000000)
  directionLo := (1764820666484401639/625000000000000000)
  directionHi := (282371306637504262241/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree033.table
  base := (-2370966630923020417463441730545971438179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-155840266001885320785609917259391235125000000000)
      constant := (1328850175700283785578706689801177822443556057749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree033.table
  base := (-4742612487521386059008138309182844317837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-311761950629032285357172580751438564000000000000)
      constant := (2659114520012831980045789181805621162683738365547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/625000000000000000)
  centralHi := (282371306637504262241/100000000000000000000)
  directionLo := (71687354359072552847/25000000000000000000)
  directionHi := (286749417436290211389/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree034.table
  base := (-508803044550610524750873751168997811969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-160552627998165151036944046030557475750000000000)
      constant := (1410040947298422530571174469978606856281318686195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree034.table
  base := (-5088618880097055645296807870824506788769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2890702276673944324680191020889209251000000000000)
      constant := (25394263664100359688798763705148090364764452922351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71687354359072552847/25000000000000000000)
  centralHi := (286749417436290211389/100000000000000000000)
  directionLo := (291061680727525819029/100000000000000000000)
  directionHi := (29106168072752581903/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree035.table
  base := (-1080455903948293590688620087874949823963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-330529979988889962576556349603447432750000000000)
      constant := (2987897425274544603631339137912710689498005851265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree035.table
  base := (-5402788877589727761071562009005386265097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-2975546997686598081145828815015471426000000000000)
      constant := (26905424526009112658929743873126939177808529107463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291061680727525819029/100000000000000000000)
  centralHi := (29106168072752581903/10000000000000000000)
  directionLo := (295310981129744873683/100000000000000000000)
  directionHi := (73827745282436218421/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree036.table
  base := (-5686356913201652561979754235482462666093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-339954703981449623079224607145779914000000000000)
      constant := (3161123204920672502547917097258369351736932550283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree036.table
  base := (-1137359495367897923243519678500469508997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-340043524299916870845718512126859289000000000000)
      constant := (3162811089077419535889403034876951004866277297535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295310981129744873683/100000000000000000000)
  centralHi := (73827745282436218421/25000000000000000000)
  directionLo := (149749999301913930721/50000000000000000000)
  directionHi := (299499998603827861443/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree037.table
  base := (-5941671721409096681517195747561469982007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-349379427974009283581892864688112395250000000000)
      constant := (3339739280504493898065204283286937810283541420817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree037.table
  base := (-2971026250473002174665543443305288464149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-1572618219855952797038552201633997888000000000000)
      constant := (15036855038023114588026542167518683153347597469371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149749999301913930721/50000000000000000000)
  centralHi := (299499998603827861443/100000000000000000000)
  directionLo := (60726245644391107553/20000000000000000000)
  directionHi := (151815614110977768883/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree038.table
  base := (-771176051546621925302332938095423819791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-44850518995821118010570140278805609562500000000)
      constant := (440466109969852972169133370879789713315602645321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree038.table
  base := (-6169737290379852234733499996224204970959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-3230081160724559350542742197394257951000000000000)
      constant := (31730504542348041112162989237577973024485224211361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60726245644391107553/20000000000000000000)
  centralHi := (151815614110977768883/50000000000000000000)
  directionLo := (153853498773552113781/50000000000000000000)
  directionHi := (307706997547104227563/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree039.table
  base := (-6370562693998762107009353123218600046991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-368228875959128604587229379772777357750000000000)
      constant := (3713077903291446001292778765630043795195886998521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree039.table
  base := (-796355819558813566414585950528682158539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-46040637246350182041783055437785001750000000000)
      constant := (464382728237186491280684665249106760240927966909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153853498773552113781/50000000000000000000)
  centralHi := (307706997547104227563/100000000000000000000)
  directionLo := (31172948196687134199/10000000000000000000)
  directionHi := (311729481966871341991/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree040.table
  base := (-3272985820900137242239525235573240692631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-188826799975844132544948818657554919500000000000)
      constant := (1953887248985809574785111419047158942414667985361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree040.table
  base := (-1636554123990045220540981944791881734271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-849942650687466715868504446411695575250000000000)
      constant := (8797189795512426442314911557347418885832385933809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31172948196687134199/10000000000000000000)
  centralHi := (311729481966871341991/100000000000000000000)
  directionLo := (39462589783556068601/12500000000000000000)
  directionHi := (315700718268448548809/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree041.table
  base := (-6696339008131401224990834693913336002873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-387078323944247925592565894857442320250000000000)
      constant := (4107808698547078010525501346172377580275221334463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree041.table
  base := (-3348275043975295201906118210714428041009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-1742307661881260309969827789886522238000000000000)
      constant := (18495011600269460875252372336396498503371262665311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39462589783556068601/12500000000000000000)
  centralHi := (315700718268448548809/100000000000000000000)
  directionLo := (319622616695212420263/100000000000000000000)
  directionHi := (39952827086901552533/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree042.table
  base := (-136445129713801205230993378802047829897/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-198251523968403793047617076199887400750000000000)
      constant := (2156586063274612000139566666920756134111255685175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree042.table
  base := (-3411219173025401494363304537744194312291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-198303335820843020911405187438850369500000000000)
      constant := (2157737398270655792178868319816641173769120662821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319622616695212420263/100000000000000000000)
  centralHi := (39952827086901552533/12500000000000000000)
  directionLo := (16174848584374371157/5000000000000000000)
  directionHi := (323496971687487423141/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree043.table
  base := (-1384844314731306624438964557803942736501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-405927771929367246597902409942107282750000000000)
      constant := (4523857737305586970926504505222189153916304356655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree043.table
  base := (-1384875634820782449500786525889604695291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-3654304765787828132870931168025568826000000000000)
      constant := (40736445760866798700324452498224645106341867111945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16174848584374371157/5000000000000000000)
  centralHi := (323496971687487423141/100000000000000000000)
  directionLo := (327325471478856037907/100000000000000000000)
  directionHi := (81831367869714009477/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree044.table
  base := (-7002652590567697910889868391002998045981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-415352495921926907100570667484439764000000000000)
      constant := (4739859607354988895783091108821933062287239269211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree044.table
  base := (-3501393684790569038847686158382487826513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-1869574743400240944668284481075915500500000000000)
      constant := (21340743865889351428174914112347100686125199153727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327325471478856037907/100000000000000000000)
  centralHi := (81831367869714009477/25000000000000000000)
  directionLo := (165554853346810521411/50000000000000000000)
  directionHi := (331109706693621042823/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree045.table
  base := (-7057901290613094734600314453271595255477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-424777219914486567603238925026772245250000000000)
      constant := (4961172755798659428901983464175546467775035004387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree045.table
  base := (-7058017231296429418686944127252022882533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-424888245312570627311356306253121464000000000000)
      constant := (4963817145728037953160451805804016558516465571923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165554853346810521411/50000000000000000000)
  centralHi := (331109706693621042823/100000000000000000000)
  directionLo := (5232049657337900031/1562500000000000000)
  directionHi := (66970235613925120397/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree046.table
  base := (-3545131733363792419396301886755888567593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-217100971953523114052953591284552363250000000000)
      constant := (2593896497079325964527913128719479476184590196783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree046.table
  base := (-7090363154770282675106948133290965379267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-3908838928825789402267844550404355351000000000000)
      constant := (46715007854533286218126304579981741357507871654893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5232049657337900031/1562500000000000000)
  centralHi := (66970235613925120397/20000000000000000000)
  directionLo := (169275651706393137559/50000000000000000000)
  directionHi := (338551303412786275119/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree047.table
  base := (-1774996965589767756024764709221917729149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-110906666974901472152143860027859301937500000000)
      constant := (1354929200046426612473023123839936620433575808819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree047.table
  base := (-3550036768533523472882775402147421728749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-1996841824919221579366741172265308763000000000000)
      constant := (24401708352310922095684598151402890264972278012771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169275651706393137559/50000000000000000000)
  centralHi := (338551303412786275119/100000000000000000000)
  directionLo := (342211423874739795127/100000000000000000000)
  directionHi := (42776427984342474391/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree048.table
  base := (-7087283662193939517373708097921403538749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-453051391892165549111243697653769689000000000000)
      constant := (5656941211789311550439256796691066924174116111419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree048.table
  base := (-7087357261329811508057994128426759835129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-453169818983455212799902237628542189000000000000)
      constant := (5659950471270283215558077873730410748612161223199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342211423874739795127/100000000000000000000)
  centralHi := (42776427984342474391/12500000000000000000)
  directionLo := (172916404816212556439/50000000000000000000)
  directionHi := (345832809632425112879/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree049.table
  base := (-1410465357765163104096399271717129349699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-462476115884725209613911955196102170250000000000)
      constant := (5899463737875810579516245347776815714371697804345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree049.table
  base := (-881548748492289031323547797990733395671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-520421636482968833958094741597892734500000000000)
      constant := (6640424759817428435608103080778010645540817944409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172916404816212556439/50000000000000000000)
  centralHi := (345832809632425112879/100000000000000000000)
  directionLo := (349416665037799171683/100000000000000000000)
  directionHi := (87354166259449792921/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree050.table
  base := (-218602037375439805048718145181592696841/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-58987604984660608764572526592304331437500000000)
      constant := (768410285424370825704792085786377311249731445484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree050.table
  base := (-1748829860719137988417119572012826090229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1062054453219101107032598931727351012750000000000)
      constant := (13838732347379596822476101938969587049052733001691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349416665037799171683/100000000000000000000)
  centralHi := (87354166259449792921/25000000000000000000)
  directionLo := (1764820666484401639/500000000000000000)
  directionHi := (352964133296880327801/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree051.table
  base := (-86452791483430770685129293084575878753/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-60165695483730566327406058785095891593750000000)
      constant := (800049385790917893082383168431878251587488544930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree051.table
  base := (-864533732924319369706534226306135473579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-60181424081792474786056021125495364250000000000)
      constant := (800474060297018338832218274687541835910351325149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1764820666484401639/500000000000000000)
  centralHi := (352964133296880327801/100000000000000000000)
  directionLo := (356476300729653362161/100000000000000000000)
  directionHi := (178238150364826681081/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree052.table
  base := (-6815305814134547954393131238948273172477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-490750287862404191121916727823099614000000000000)
      constant := (6658800664707494734660448100606621613244559531387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree052.table
  base := (-1363069147088356597683296395838712011789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-4417907254901711941061671315161928401000000000000)
      constant := (59960993618291904271433735344319765679683199544655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356476300729653362161/100000000000000000000)
  centralHi := (178238150364826681081/50000000000000000000)
  directionLo := (44994275081978939931/12500000000000000000)
  directionHi := (359954200655831519449/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree053.table
  base := (-1338520141536658954067395603029684036869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3172952257194762979153335173150000000000000)
      linear := (-178061591973999235181411529143977250000000000)
      constant := (2464399349263956353980017349020912118538216855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree053.table
  base := (-1673158733962417245161190949900229636919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7139142578688216703095004139587500000000000)
      linear := (-400743322883087014731871583240316000000000000)
      constant := (5547837488526262054346821559626444012852621889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44994275081978939931/12500000000000000000)
  centralHi := (359954200655831519449/100000000000000000000)
  directionLo := (36339881694587143819/10000000000000000000)
  directionHi := (363398816945871438191/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree054.table
  base := (-6548182037386203905683031541913932822151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-509599735847523512127253242907764576500000000000)
      constant := (7191485360060699197066459879506103561127444896481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree054.table
  base := (-327410568709327895388212955498438832639/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-127433241581306095944248525094845909750000000000)
      constant := (1798823559183473404796525322021098542218345220045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36339881694587143819/10000000000000000000)
  centralHi := (363398816945871438191/100000000000000000000)
  directionLo := (366811087271826253927/100000000000000000000)
  directionHi := (45851385908978281741/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree055.table
  base := (-6382112077971323628987246381526017121201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-519024459840083172629921500450097057750000000000)
      constant := (7465762546821558538347311836367482970721587857031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree055.table
  base := (-6382137214045999884707330994637081984339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-4672441417939673210458584697540714926000000000000)
      constant := (67227424024640877809099103827117699249539139660381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366811087271826253927/100000000000000000000)
  centralHi := (45851385908978281741/12500000000000000000)
  directionLo := (370191906088476891907/100000000000000000000)
  directionHi := (92547976522119222977/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree056.table
  base := (-6194443210852449302371280977729315982831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-528449183832642833132589757992429539000000000000)
      constant := (7745328590635359620913365721860179233428711941561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree056.table
  base := (-309723237039710612310851059432942191337/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1189321534738081741731055622916744275250000000000)
      constant := (17436205759965497343189311091038886399654698482115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370191906088476891907/100000000000000000000)
  centralHi := (92547976522119222977/25000000000000000000)
  directionLo := (373542127371599216513/100000000000000000000)
  directionHi := (186771063685799608257/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree057.table
  base := (-1197043899330908451878677130790530731527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-537873907825202493635258015534762020250000000000)
      constant := (8030182867596206746662971340060135538389107759685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree057.table
  base := (-2992618966052473660230657392981753238419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-269007269998054484632770015877402182000000000000)
      constant := (4017213309538152456953906335555410573290189667189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373542127371599216513/100000000000000000000)
  centralHi := (186771063685799608257/50000000000000000000)
  directionLo := (376862567137120174179/100000000000000000000)
  directionHi := (18843128356856008709/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree058.table
  base := (-5754477997615917537279387675681588236677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-547298631817762154137926273077094501500000000000)
      constant := (8320324852896541856393769685723268515973991681587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree058.table
  base := (-5754493778623095989389589708549581773427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-4926975580977634479855498079919501451000000000000)
      constant := (74922468905971094701463652687259923702880585737533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376862567137120174179/100000000000000000000)
  centralHi := (18843128356856008709/5000000000000000000)
  directionLo := (76030801152443676919/20000000000000000000)
  directionHi := (95038501440554596149/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree059.table
  base := (-220089995587516166663866883477944938117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-556723355810321814640594530619426982750000000000)
      constant := (8615754105079625395258320420738005471831405955675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree059.table
  base := (-5502263394547872497366367863116697045909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-5011820301990288236321135874045763626000000000000)
      constant := (77582707077474168241330579955715525152598150212411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76030801152443676919/20000000000000000000)
  centralHi := (95038501440554596149/25000000000000000000)
  directionLo := (76683438025414882109/20000000000000000000)
  directionHi := (191708595063537205273/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree060.table
  base := (-5228561397805348629622312914811954917447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-566148079802881475143262788161759464000000000000)
      constant := (8916470252795947923078524672055691783273569431457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree060.table
  base := (-261428647579111255978095110461480997467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-141574028416748388688521490782556272250000000000)
      constant := (2230293076412064832122196452062291921677893540385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76683438025414882109/20000000000000000000)
  centralHi := (191708595063537205273/50000000000000000000)
  directionLo := (193326417796961652673/50000000000000000000)
  directionHi := (386652835593923305347/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree061.table
  base := (-4933434582467373477662754385761963147481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-575572803795441135645931045704091945250000000000)
      constant := (9222472983665113640176172018640149385302084615711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree061.table
  base := (-2466722232182024497486576767016646110161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-2590754872007797874626205731149143988000000000000)
      constant := (41522998560236327112958425272874883581964848605119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193326417796961652673/50000000000000000000)
  centralHi := (386652835593923305347/100000000000000000000)
  directionLo := (389861627838264999727/100000000000000000000)
  directionHi := (24366351739891562483/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree062.table
  base := (-461688800128508838809586383828241400841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-292498763894000398074299651623212213250000000000)
      constant := (4766881017454106498621028191059433974753348489355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree062.table
  base := (-923379290202941770588697245046462436149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-5266354465028249505718049256424550151000000000000)
      constant := (85849043826411576266180643081410991394339030286855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389861627838264999727/100000000000000000000)
  centralHi := (24366351739891562483/6250000000000000000)
  directionLo := (393044224545511164653/100000000000000000000)
  directionHi := (196522112272755582327/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree063.table
  base := (-85578745307707215783576171458103838457/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-297211125890280228325633780394378453875000000000)
      constant := (4925168592734525635525730449027521101287348269175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree063.table
  base := (-267434030542199735627965511066820206741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-74322210917234767530328986813205726750000000000)
      constant := (1231940123381618879763116139273563579612990001542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393044224545511164653/100000000000000000000)
  centralHi := (196522112272755582327/50000000000000000000)
  directionLo := (396201256984960307897/100000000000000000000)
  directionHi := (198100628492480153949/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree064.table
  base := (-19597977536964956476210601508764446451/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-75480871971640014644241977291386173625000000000)
      constant := (1271524781173430233914270176943144610926559744525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree064.table
  base := (-3919601680735656529906489725239209773813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-5436043907053557018649324844677074501000000000000)
      constant := (91597930621751632893690031865599533081587205310427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396201256984960307897/100000000000000000000)
  centralHi := (198100628492480153949/50000000000000000000)
  directionLo := (399333331471770481923/100000000000000000000)
  directionHi := (99833332867942620481/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree065.table
  base := (-3538873775051721712280879121925498868471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-613271699765679777656604075873421870250000000000)
      constant := (10499345070225466345364902387245739696667829368401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree065.table
  base := (-1769439524902037594204255800492342249537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-2760444314033105387557481319401668338000000000000)
      constant := (47271883818249435021795774760216675176428943174223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399333331471770481923/100000000000000000000)
  centralHi := (99833332867942620481/25000000000000000000)
  directionLo := (201220515363259664903/50000000000000000000)
  directionHi := (402441030726519329807/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree066.table
  base := (-3136781362306815457451410926793182119879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-622696423758239438159272333415754351500000000000)
      constant := (10831777516379289086467232739087593164478485100449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree066.table
  base := (-392098233527994192056487897920511851821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-77857407626095340716397228235133317375000000000)
      constant := (1354683315917176551249313892962230037861711682251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201220515363259664903/50000000000000000000)
  centralHi := (402441030726519329807/100000000000000000000)
  directionLo := (81104983028197135161/20000000000000000000)
  directionHi := (202762457570492837903/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree067.table
  base := (-2713326087790777747658956988594781962157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-632121147750799098661940590958086832750000000000)
      constant := (11169495477135752471856392597670040266764892775467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree067.table
  base := (-135666496803561571214353566174161482991/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1422644517522879572011559556763965256500000000000)
      constant := (25144555739077904035686690026041856981696306653445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81104983028197135161/20000000000000000000)
  centralHi := (202762457570492837903/50000000000000000000)
  directionLo := (408585523957939546941/100000000000000000000)
  directionHi := (204292761978969773471/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree068.table
  base := (-1134257264536121032057704392600031548329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-320772935871679379582304424250209657000000000000)
      constant := (5756249429677686521169681627428392687682829692399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree068.table
  base := (-453703562996108225546799139931282548421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-5775422791104172044511876021182123201000000000000)
      constant := (103666839431098885618473839220700477825742358058295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408585523957939546941/100000000000000000000)
  centralHi := (204292761978969773471/50000000000000000000)
  directionLo := (411623376371974711951/100000000000000000000)
  directionHi := (25726461023248419497/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree069.table
  base := (-1802352219698349890576812363621776081729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-650970595735918419667277106042751795250000000000)
      constant := (11860787584682188105039248343850345997219747047799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree069.table
  base := (-450588756205606789144774425280564176797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-162785208669911827804930939314121816000000000000)
      constant := (2966751318526050616714068242108005849872458601307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411623376371974711951/100000000000000000000)
  centralHi := (25726461023248419497/6250000000000000000)
  directionLo := (103659743139436942311/25000000000000000000)
  directionHi := (82927794511549553849/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree070.table
  base := (-1314843814942938389055546027943508156769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-660395319728478080169945363585084276500000000000)
      constant := (12214361587196733384463472207772965146891022466039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree070.table
  base := (-1314846209136244802657603188879898173459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-5945112233129479557443151609434647551000000000000)
      constant := (109986846472048707630693732524626361685449263208861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103659743139436942311/25000000000000000000)
  centralHi := (82927794511549553849/20000000000000000000)
  directionLo := (417632794631390346879/100000000000000000000)
  directionHi := (652551241611547417/156250000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree071.table
  base := (-201498307808196117031518902645004959501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442016608334660246401592863587500000000000)
      linear := (-33218609587434920684021703091024437500000000)
      constant := (623547947403379480433511349997665350990636691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree071.table
  base := (-805995274284350341298937954519112015067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (4449456)
      previous := (2224728)
      next := (2224728)
      square := (15912597900047768870457343089150000000000000)
      linear := (-1196182692747893932534971117548286000000000000)
      constant := (22459479458162821195112832741118448954147091173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417632794631390346879/100000000000000000000)
  centralHi := (652551241611547417/156250000000000000)
  directionLo := (420605307550327310209/100000000000000000000)
  directionHi := (42060530755032731021/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree072.table
  base := (-275803763433679145225004911574772485961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-679244767713597401175281878669749239000000000000)
      constant := (12937365210761363048907216047995565348462242112591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree072.table
  base := (-275805506503571873003713940680389510383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-679422408350531896708269688631907989000000000000)
      constant := (12944135053087224944885921093171395567547149465273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420605307550327310209/100000000000000000000)
  centralHi := (42060530755032731021/10000000000000000000)
  directionLo := (5294461999453204917/1250000000000000000)
  directionHi := (423556959956256393361/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree073.table
  base := (137860908243303212378134537429689214993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-344334745853078530838975068106040860125000000000)
      constant := (6653397372952029449347282204808371362366621963817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree073.table
  base := (8616260301062970567562226137074294473/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-774955799520930103355008123976679259500000000000)
      constant := (14977973088410770748432443630050099741701189053732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5294461999453204917/1250000000000000000)
  centralHi := (423556959956256393361/100000000000000000000)
  directionLo := (213244092482808383653/50000000000000000000)
  directionHi := (426488184965616767307/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree074.table
  base := (848581176460380678256922484749140051599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-698094215698716722180618393754414201500000000000)
      constant := (13681509383847358760843472438523361427829060560231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree074.table
  base := (848579908397305736022447441951268590277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-6284491117180094583305702785939696251000000000000)
      constant := (123197943340707496672982859101897298701024426691317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213244092482808383653/50000000000000000000)
  centralHi := (426488184965616767307/100000000000000000000)
  directionLo := (21469970045574498779/5000000000000000000)
  directionHi := (429399400911489975581/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree075.table
  base := (721386177249557043027837420410192681497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-353759469845638191341643325648373341375000000000)
      constant := (7030754548404586740579338182380409579938654442993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree075.table
  base := (1442771273225182046540352476868753260967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-707703982021416482196815620007328714000000000000)
      constant := (14068854569855765748736628308892923452619593823423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21469970045574498779/5000000000000000000)
  centralHi := (429399400911489975581/100000000000000000000)
  directionLo := (216145506020265695549/50000000000000000000)
  directionHi := (432291012040531391099/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree076.table
  base := (2058293699956872377101534141381391497851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-716943663683836043185954908839079164000000000000)
      constant := (14446793861416077671199202333967512839189733296819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree076.table
  base := (257286597264869746464090650428378858359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-806772569900675262029622296774027575125000000000)
      constant := (16261128482687596884283025347011691590898514524039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216145506020265695549/50000000000000000000)
  centralHi := (432291012040531391099/100000000000000000000)
  directionLo := (27197713073013718107/6250000000000000000)
  directionHi := (435163409168219489713/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree077.table
  base := (134757191205895350452892932155664612041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-181592096919098925922155791595352911312500000000)
      constant := (3709340914500905409661014961041398174817146849645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree077.table
  base := (2695143038340926579713872510498194998699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-6539025280218055852702616168318482776000000000000)
      constant := (133605953362631067122442393453107601243513793581179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27197713073013718107/6250000000000000000)
  centralHi := (435163409168219489713/100000000000000000000)
  directionLo := (43801697029542996043/10000000000000000000)
  directionHi := (438016970295429960431/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree078.table
  base := (83833038965695889086388234776705988787/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-91974138958619420523911427990468015812500000000)
      constant := (1904152308753463734569637181208986728209398875015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree078.table
  base := (1676660444470461884142049149039302024131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-367992777846150533842680775691374719500000000000)
      constant := (7620581526868319282265147311283126912803737038139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43801697029542996043/10000000000000000000)
  centralHi := (438016970295429960431/100000000000000000000)
  directionLo := (440852061189088612839/100000000000000000000)
  directionHi := (11021301529727215321/2500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree079.table
  base := (4032825920523026473054895333645634950761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-745217835661515024693959681466076607750000000000)
      constant := (15634358283569411241092466828094724023444769938609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree079.table
  base := (2016412674933836181230742295883475261323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-3354357361121681682816945878285503563000000000000)
      constant := (70391285049798794764042623641162320298381375592283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440852061189088612839/100000000000000000000)
  centralHi := (11021301529727215321/2500000000000000000)
  directionLo := (443669035929428242177/100000000000000000000)
  directionHi := (221834517964714121089/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree080.table
  base := (4733656082810608660677635179960702827071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-754642559654074685196627939008409089000000000000)
      constant := (16040783086918366916002110906818856710390103134999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree080.table
  base := (4733655596619186271775678941617307974119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-6793559443256017122099529550697269301000000000000)
      constant := (144442261105458807289489795169165484508147153994999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443669035929428242177/100000000000000000000)
  centralHi := (221834517964714121089/50000000000000000000)
  directionLo := (1744016552445966677/390625000000000000)
  directionHi := (446468237426167469313/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree081.table
  base := (1363952837429475218678530331793760355781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-191016820911658586424824049137685392562500000000)
      constant := (4113123217555579537295026459240258809484530961989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree081.table
  base := (5455810935552636511449965931739942154617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-764267129363185653173907482758170164000000000000)
      constant := (16461060045868278134269273867292631207084600850273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1744016552445966677/390625000000000000)
  centralHi := (446468237426167469313/100000000000000000000)
  directionLo := (112312499476435448041/25000000000000000000)
  directionHi := (89849999581148358433/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree082.table
  base := (1239858227173999073505592674157229451799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-773492007639194006201964454093074051500000000000)
      constant := (16869487625192257318560510979843525795890005970155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree082.table
  base := (1549822695778450465208058062767602800773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1740812221320331158757701284737448412750000000000)
      constant := (37976101986823909936638968564875707765954371095733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112312499476435448041/25000000000000000000)
  centralHi := (89849999581148358433/20000000000000000000)
  directionLo := (22600731968577332049/5000000000000000000)
  directionHi := (452014639371546640981/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree083.table
  base := (3482047474385969228177513211599066475949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-391458365815876833352316355817703266375000000000)
      constant := (8645883672427186324174106899159587307600266025381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree083.table
  base := (6964094648363744951689894320123961596073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-7048093606293978391496442933076055826000000000000)
      constant := (155706863646336212007555725997643773722974130747033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22600731968577332049/5000000000000000000)
  centralHi := (452014639371546640981/100000000000000000000)
  directionLo := (227381237019498665147/50000000000000000000)
  directionHi := (90952494807799466059/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree084.table
  base := (1937555593517740060434508339826703572933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-198085363906078331801825242294434753500000000000)
      constant := (4429833005835339722787196560004168076211885105677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree084.table
  base := (7750222118279199758772214117234432638069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-792548703034070238662453414133590889000000000000)
      constant := (17728545273033322973419715728911426929774172873661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227381237019498665147/50000000000000000000)
  centralHi := (90952494807799466059/20000000000000000000)
  directionLo := (114373451186767464487/25000000000000000000)
  directionHi := (457493804747069857949/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree085.table
  base := (4278836531578744523773748239175397583451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-400883089808436493854984613360035747625000000000)
      constant := (9076090827858422798505310746604908033607451513219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree085.table
  base := (2139418211346574315135346970660594150723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1804445762079821476106929630332145044000000000000)
      constant := (40863634833976031407590365369259193596613092369683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114373451186767464487/25000000000000000000)
  centralHi := (457493804747069857949/100000000000000000000)
  directionLo := (23010446267392905399/5000000000000000000)
  directionHi := (460208925347858107981/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree086.table
  base := (4693223361366871047228089257067891278417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-405595451804716324106318742131201988250000000000)
      constant := (9295158118913843297226578085953098363147885772473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree086.table
  base := (2346611634339297173626746984907106198271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-1825656942332984915223339078863710587750000000000)
      constant := (41849939811223540734839509474270989285366183810191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23010446267392905399/5000000000000000000)
  centralHi := (460208925347858107981/100000000000000000000)
  directionLo := (462908121075565917809/100000000000000000000)
  directionHi := (46290812107556591781/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree087.table
  base := (1279567888254701781342548954958577206127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-102576953450249038589413217725592057218750000000)
      constant := (2379216970772461096501926949396543548932642092963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree087.table
  base := (10236542948257949567006869591223430303159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-820830276704954824150999345509011614000000000000)
      constant := (19043618572547536142755079137782284273477452673871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462908121075565917809/100000000000000000000)
  centralHi := (46290812107556591781/10000000000000000000)
  directionLo := (465591668896245557743/100000000000000000000)
  directionHi := (29099479306015347359/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree088.table
  base := (2776990501364789751136471606072748132953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-207510087898637992304493499836767234750000000000)
      constant := (4870610059458265050252145771925498910357048949057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree088.table
  base := (11107961871185627780614647748665525075973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-7472317211357247173824631903707366701000000000000)
      constant := (175432963033637085751988325804663045873945639674933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465591668896245557743/100000000000000000000)
  centralHi := (29099479306015347359/6250000000000000000)
  directionLo := (18730393513579857993/4000000000000000000)
  directionHi := (234129918919748224913/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree089.table
  base := (1200070324632865667698091379283577958591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-419732537793555814860321128444700710125000000000)
      constant := (9968214825157224065798462874942589122931461559395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree089.table
  base := (1200070313207392060175162571076666851093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-3778580966184950465145134848916814438000000000000)
      constant := (89760473432419334982861075855077166489130362162265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18730393513579857993/4000000000000000000)
  centralHi := (234129918919748224913/50000000000000000000)
  directionLo := (235456444656624269103/50000000000000000000)
  directionHi := (470912889313248538207/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree090.table
  base := (12914766681690344671560816189063802445569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-848889799579671290223310514431733901500000000000)
      constant := (20395704001542934129890342024818422463005620341161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree090.table
  base := (1614345823060247044737176846311457118101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-106138981296979926204943159610554042375000000000)
      constant := (2550784980942637959059941634946925416928563119069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235456444656624269103/50000000000000000000)
  centralHi := (470912889313248538207/100000000000000000000)
  directionLo := (118387769350668205803/25000000000000000000)
  directionHi := (473551077402672823213/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree091.table
  base := (138501521879053948575944806609163660741/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-214578630893057737681494692993516595687500000000)
      constant := (5215065822441942873649072916575622068304327505725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree091.table
  base := (54102156660977608957770766325717871983/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-965856421799401055402693160760769153250000000000)
      constant := (23479959788378767485568164678383477101794822796576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118387769350668205803/25000000000000000000)
  centralHi := (473551077402672823213/100000000000000000000)
  directionLo := (3809397193233491827/800000000000000000)
  directionHi := (59521831144273309797/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree092.table
  base := (7403429830476274267230403694812192873007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-433869623782395305614323514758199432000000000000)
      constant := (10665053756758000811460629747968868032404874658183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree092.table
  base := (185085744882653239669247229408810007809/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-976462011925982774960897885026551925125000000000)
      constant := (24008803236138802282980660677712111734077008374890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3809397193233491827/800000000000000000)
  centralHi := (59521831144273309797/12500000000000000000)
  directionLo := (119695961211362762387/25000000000000000000)
  directionHi := (478783844845451049549/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree093.table
  base := (631395560532628152270725781871412088929/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-877163971557350271731315287058731345250000000000)
      constant := (21805236671548381721805279402644826598939129225025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree093.table
  base := (15784888953491426898663636595294810573063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-877393424046723995128091208259853064000000000000)
      constant := (21816529040333145626101713397508797702662558927647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119695961211362762387/25000000000000000000)
  centralHi := (478783844845451049549/100000000000000000000)
  directionLo := (3851031185937591353/800000000000000000)
  directionHi := (240689449121099459563/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree094.table
  base := (1049015010710332463094802057421829342891/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-110823586943738741529247943075132978312500000000)
      constant := (2785706345352788130442935303377008868643209767158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree094.table
  base := (16784240120490730380610582857731418416983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-7981385537433169712618458668464939751000000000000)
      constant := (200674684719345084156424449264477741041547725751143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851031185937591353/800000000000000000)
  centralHi := (240689449121099459563/50000000000000000000)
  directionLo := (483960036842664995381/100000000000000000000)
  directionHi := (241980018421332497691/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree095.table
  base := (4451228268288819860696542258651262035937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-224003354885617398184162950535849076937500000000)
      constant := (5692837446615151029524851080326119845412073868353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree095.table
  base := (17804913029896370838186565465484971936847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-8066230258445823469084096462591201926000000000000)
      constant := (205048195950285838445009055340837923186899097624287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483960036842664995381/100000000000000000000)
  centralHi := (241980018421332497691/50000000000000000000)
  directionLo := (121631870527586749401/25000000000000000000)
  directionHi := (97305496422069399521/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree096.table
  base := (18846907666569297883715224244305144921949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-905438143535029253239320059685728789000000000000)
      constant := (23262333741725303527736996472328437533664289649381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree096.table
  base := (9423453814895043843896893340389220145793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-452837498858804290308318569817636894500000000000)
      constant := (11637183058289112855790065989483725655042633519017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121631870527586749401/25000000000000000000)
  centralHi := (97305496422069399521/20000000000000000000)
  directionLo := (489081449695768338569/100000000000000000000)
  directionHi := (48908144969576833857/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree097.table
  base := (19910223907761402593710413682879232380057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-914862867527588913741988317228061270250000000000)
      constant := (23758602627995536897004482296084123388646566849633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree097.table
  base := (9955111938247338105785638849799766323439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-4117959850235565491007686025421863138000000000000)
      constant := (106968991005266686815894134471584139803266144110719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489081449695768338569/100000000000000000000)
  centralHi := (48908144969576833857/10000000000000000000)
  directionLo := (491622149647872084113/100000000000000000000)
  directionHi := (245811074823936042057/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree098.table
  base := (52487154399609597840011706332753700759/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-115535948940018571780582071846299218937500000000)
      constant := (3032519555593620923630842560340919384949112163550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree098.table
  base := (20994861733266190916291167517355251019817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-8320764421483784738481009844969988451000000000000)
      constant := (218454256829591160826512243657804446985302279621657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491622149647872084113/100000000000000000000)
  centralHi := (245811074823936042057/50000000000000000000)
  directionLo := (494149786615632458921/100000000000000000000)
  directionHi := (247074893307816229461/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree099.table
  base := (22100821191783138616238009302240847936691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-933712315512708234747324832312726232750000000000)
      constant := (24766995191546155839663389981077428797854033360779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree099.table
  base := (22100821169193685045670876338514165802667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-933956571388493166105183071010694514000000000000)
      constant := (24779791055826450546469160408852129948284785370723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494149786615632458921/100000000000000000000)
  centralHi := (247074893307816229461/50000000000000000000)
  directionLo := (496664560040431564233/100000000000000000000)
  directionHi := (248332280020215782117/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree100.table
  base := (2903512772183915332696418605871209343509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-117892129938158486906249136231882339250000000000)
      constant := (3159889858502176107855835612763274455991591493021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree100.table
  base := (2322810215827355037423361488286229552941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-4245226931754546125706142716611256400500000000000)
      constant := (113814785012880058261587998016347741125409755316305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496664560040431564233/100000000000000000000)
  centralHi := (248332280020215782117/50000000000000000000)
  directionLo := (124791666084928275601/25000000000000000000)
  directionHi := (99833332867942620481/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree101.table
  base := (12188352347472229532908871790184466984219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-476280881748913777876330673698695597625000000000)
      constant := (12898263736925856733326237540393525010730055123011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree101.table
  base := (761772021207210898322853661814407310399/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1071912323065218250984740403418596872000000000000)
      constant := (29036076049596194688360509556082526153043695707516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124791666084928275601/25000000000000000000)
  centralHi := (99833332867942620481/20000000000000000000)
  directionLo := (125414072270597929073/25000000000000000000)
  directionHi := (501656289082391716293/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree102.table
  base := (25546628725725190442798232484755811346383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-961986487490387216255329604939723676500000000000)
      constant := (26319221008787427147819068164865191280240650818727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree102.table
  base := (12773314355931812210433501910273967435753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-481119072529688875796864501193057619500000000000)
      constant := (13166401922951180159599050203548204416690759122257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125414072270597929073/25000000000000000000)
  centralHi := (501656289082391716293/100000000000000000000)
  directionLo := (63016702394558227893/12500000000000000000)
  directionHi := (100826723831293164629/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree103.table
  base := (835558570445923982298211690105358395321/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-121426401435368359594749732810257019718750000000)
      constant := (3355899934075555619562000837636588087833842614496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree103.table
  base := (26737874242492685865870952078163226498709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-8744988026547053520809198815601299326000000000000)
      constant := (241749448672842442675731636087383176139887979496389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63016702394558227893/12500000000000000000)
  centralHi := (100826723831293164629/20000000000000000000)
  directionLo := (253299417464626674203/50000000000000000000)
  directionHi := (506598834929253348407/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree104.table
  base := (27950441267501638638691493928731255330267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-980835935475506537260666120024388639000000000000)
      constant := (27380462865117609211032568375474426012058731535123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree104.table
  base := (5590088251499371605257913293263268843401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-8829832747559707277274836609727561501000000000000)
      constant := (246551250574273731305659084774131745528174671264605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253299417464626674203/50000000000000000000)
  centralHi := (506598834929253348407/100000000000000000000)
  directionLo := (509052112400643359251/100000000000000000000)
  directionHi := (127263028100160839813/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree105.table
  base := (5836865950884374980771576164301139493567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-990260659468066197763334377566721120250000000000)
      constant := (27919011186171164719682213098107457171037103164115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree105.table
  base := (14592164872961662238921008429249285537531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-495259859365131168541137466880767982000000000000)
      constant := (13966702239778848065456728855647138575403194802739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509052112400643359251/100000000000000000000)
  centralHi := (127263028100160839813/25000000000000000000)
  directionLo := (255746811674866045931/50000000000000000000)
  directionHi := (511493623349732091863/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree106.table
  base := (15219769852888857227191905472490964638571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1586476128597381489576667586575000000000000)
      linear := (-177943286482845471389462911197766750000000000)
      constant := (5066366044078692353868430387775759874618036411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree106.table
  base := (1902471231159955105901199887541761361231/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3569571289344108351547502069793750000000000)
      linear := (-400477135527991046199987192861342375000000000)
      constant := (11405198375618767826600935938496687342395378478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255746811674866045931/50000000000000000000)
  centralHi := (511493623349732091863/100000000000000000000)
  directionLo := (25696176773759455357/5000000000000000000)
  directionHi := (513923535475189107141/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree107.table
  base := (7929017778446593441426604791835879427201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-252277526863296379692167723162846520687500000000)
      constant := (7252990653349047613521557253833495864200836231969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree107.table
  base := (15858035553827890430785245355660045635873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-4542183455298834273335874996053174013000000000000)
      constant := (130621091657971624873029845017265620311077567282833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25696176773759455357/5000000000000000000)
  centralHi := (513923535475189107141/100000000000000000000)
  directionLo := (103268402505935631381/20000000000000000000)
  directionHi := (258171006264839078453/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree108.table
  base := (6602784794380326516551801897980362501283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1018534831445745179271339150193718564000000000000)
      constant := (29566365719364759564719406866923695548622149984135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree108.table
  base := (33013923966695391756958025558705749045533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1018801292401146922570820865136956689000000000000)
      constant := (29581592952478174599747265121748112664756335975077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103268402505935631381/20000000000000000000)
  centralHi := (258171006264839078453/50000000000000000000)
  directionLo := (259374607224318834659/50000000000000000000)
  directionHi := (518749214448637669319/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree109.table
  base := (34333098274617616955860241795965679241811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1027959555438304839774007407736051045250000000000)
      constant := (30126053753461836870312190201094529066756023126059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree109.table
  base := (34333098270196734873497644455892182014731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-9254056352622976059603025580358872376000000000000)
      constant := (271274077665287360212812285186411385525091163045851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259374607224318834659/50000000000000000000)
  centralHi := (518749214448637669319/100000000000000000000)
  directionLo := (521145297473707452183/100000000000000000000)
  directionHi := (65143162184213431523/12500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree110.table
  base := (35673594017303710905146295353564041141101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1037384279430864500276675665278383526500000000000)
      constant := (30691026715621852066015606719296069860974693006069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree110.table
  base := (35673594013550031454732750271111627393007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-9338901073635629816068663374485134551000000000000)
      constant := (276361406594307138975124069997609634140750076843647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521145297473707452183/100000000000000000000)
  centralHi := (65143162184213431523/12500000000000000000)
  directionLo := (523530414271071159727/100000000000000000000)
  directionHi := (32720650891941947483/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree111.table
  base := (37035411196065658477535179305579643655339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1046809003423424160779343922820716007750000000000)
      constant := (31261284605789661829404759360135082754049065492291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree111.table
  base := (18517705596439374741584293373692288671033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-523541433036015754029683398256188707000000000000)
      constant := (15638684631048270919341445010134112471391112684577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523530414271071159727/100000000000000000000)
  centralHi := (32720650891941947483/6250000000000000000)
  directionLo := (262952357022484087823/50000000000000000000)
  directionHi := (525904714044968175647/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree112.table
  base := (38418549807628701380832810138916638984333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1056233727415983821282012180363048489000000000000)
      constant := (31836827423918895029628028520266016827930143632277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree112.table
  base := (19209274902461602352428811126908450830807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-4754295257830468664499969481368829450500000000000)
      constant := (143339413979278576906287641027793899007631757737447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262952357022484087823/50000000000000000000)
  centralHi := (525904714044968175647/100000000000000000000)
  directionLo := (528268342646613743863/100000000000000000000)
  directionHi := (66033542830826717983/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree113.table
  base := (995575246230981412724284904912219842253/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-133207306426067935223085054738172621281250000000)
      constant := (4052206896246320058068493668045967621195365041285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree113.table
  base := (4977876230867829108719368770731426798599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1199179404584198885683197094607990134500000000000)
      constant := (36488615049127835450460467299824301375104242229079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528268342646613743863/100000000000000000000)
  centralHi := (66033542830826717983/12500000000000000000)
  directionLo := (21224857707150093901/4000000000000000000)
  directionHi := (265310721339376173763/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree114.table
  base := (2062439565929109611551135749924968870131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-268770793850275785571837173861928362875000000000)
      constant := (8250941960977968869753333143814183597814907560695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree114.table
  base := (41248791316632802188178077341086776801827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1075364439742916093547912727887798139000000000000)
      constant := (33020733406885756790828632242032685249179149828763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21224857707150093901/4000000000000000000)
  centralHi := (265310721339376173763/50000000000000000000)
  directionLo := (266482076798028210913/50000000000000000000)
  directionHi := (532964153596056421827/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree115.table
  base := (42695894213711228895818769677115379449403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1084507899393662802790016952990045932750000000000)
      constant := (33595165445715280424242378329893010998119860929107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree115.table
  base := (42695894212056700097840648358412672759579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-9763124678698898598396852345116445426000000000000)
      constant := (302511868765157680526763257022274172542781015079659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266482076798028210913/50000000000000000000)
  centralHi := (532964153596056421827/100000000000000000000)
  directionLo := (267648305900785209619/50000000000000000000)
  directionHi := (535296611801570419239/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree116.table
  base := (2208215926649519078118852815347410646251/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-273483155846555615823171302633094603500000000000)
      constant := (8547961993839402369247329831662476252222816882095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree116.table
  base := (8832863706317243945110242764456059386319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-9847969399711552354862490139242707601000000000000)
      constant := (307884724702372803415330366495371156520294099755995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267648305900785209619/50000000000000000000)
  centralHi := (535296611801570419239/100000000000000000000)
  directionLo := (537618950739388964033/100000000000000000000)
  directionHi := (268809475369694482017/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree117.table
  base := (45654064275044693247661383841887544054379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1103357347378782123795353468074710895250000000000)
      constant := (34793815432819393014006632967198207304672139330051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree117.table
  base := (45654064273853100625310143262246244583967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1103646013413800679036458659263218864000000000000)
      constant := (34811685385938089621199631924999318459049307410423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537618950739388964033/100000000000000000000)
  centralHi := (268809475369694482017/50000000000000000000)
  directionLo := (539931300983747279173/100000000000000000000)
  directionHi := (269965650491873639587/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree118.table
  base := (47165131438718784867937853522501313799061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1112782071371341784298021725617043376500000000000)
      constant := (35401067818084270672209582094075469585460485801309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree118.table
  base := (47165131437707655333840985108165631032283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-10017658841736859867793765727495231951000000000000)
      constant := (318773200078221172134167636879560199081678945622443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539931300983747279173/100000000000000000000)
  centralHi := (269965650491873639587/50000000000000000000)
  directionLo := (271116895162346095019/50000000000000000000)
  directionHi := (542233790324692190039/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree119.table
  base := (48697520023041981850857301981246789141953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1122206795363901444800689983159375857750000000000)
      constant := (36013605131138497535609699826988677637012106970057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree119.table
  base := (48697520022184046295361543763158735886361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-10102503562749513624259403521621494126000000000000)
      constant := (324288819516584812238295409807484300950420128995081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271116895162346095019/50000000000000000000)
  centralHi := (542233790324692190039/100000000000000000000)
  directionLo := (272263271925246378687/50000000000000000000)
  directionHi := (4356212350803942059/800000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree120.table
  base := (10050246005439794821248363289697235864091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1131631519356461105303358240701708339000000000000)
      constant := (36631427371970528675542661681052502273341947956895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree120.table
  base := (50251230026471073743819546425299554726929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1131927587084685264525004590638639589000000000000)
      constant := (36650225198714482930128828921931310000558063491001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272263271925246378687/50000000000000000000)
  centralHi := (4356212350803942059/800000000000000000)
  directionLo := (273404842013470460887/50000000000000000000)
  directionHi := (21872387361077636871/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree121.table
  base := (51826261450505131548571030078846482903627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1141056243349020765806026498244040820250000000000)
      constant := (37254534540570669614295014808794464926150656532963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree121.table
  base := (25913130724943800030133322224900841219349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-5136096502387410568595339554937009238000000000000)
      constant := (167731410946835484659295346188761399028735831189829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273404842013470460887/50000000000000000000)
  centralHi := (21872387361077636871/4000000000000000000)
  directionLo := (109816666154736882529/20000000000000000000)
  directionHi := (274541665386842206323/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree122.table
  base := (53422614292385736613986096913429292145569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1150480967341580426308694755786373301500000000000)
      constant := (37882926636930782254035249659291597087925379641161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree122.table
  base := (53422614291861874881761604003917064181027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-10357037725787474893656316904000280651000000000000)
      constant := (341121204832233816344703573174645253389084700222067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109816666154736882529/20000000000000000000)
  centralHi := (274541665386842206323/50000000000000000000)
  directionLo := (137836900384431637057/25000000000000000000)
  directionHi := (551347601537726548229/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree123.table
  base := (55040288552358512374451463680458697149177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1159905691334140086811363013328705782750000000000)
      constant := (38516603661044037471957581960207048944394352030913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree123.table
  base := (13760072137978535494765117653706008518197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-290052290188892462503387630503515078500000000000)
      constant := (9634088211223826294053723012518833603839359095293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137836900384431637057/25000000000000000000)
  centralHi := (551347601537726548229/100000000000000000000)
  directionLo := (8650040802565943667/1562500000000000000)
  directionHi := (553602611364220394689/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree124.table
  base := (28339642115009461712959359706939166123807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-584665207663349873657015635435519132000000000000)
      constant := (19577782806452353489187101464040004547094682043383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree124.table
  base := (28339642114821003568608683317970810449953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-5263363583906391203293796246126402500500000000000)
      constant := (176290367104545739155743877312830443841844704698513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8650040802565943667/1562500000000000000)
  centralHi := (553602611364220394689/100000000000000000000)
  directionLo := (555848472964678029413/100000000000000000000)
  directionHi := (277924236482339014707/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree125.table
  base := (58339601325027809664337661487496514947553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1178755139319259407816699528413370745250000000000)
      constant := (39799812492507988208893704109239359486810564116457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree125.table
  base := (3646225082794258056593283810251929082661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1326446486103179520381653785797383397000000000000)
      constant := (44797735080911502526723266405479460777597530134762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555848472964678029413/100000000000000000000)
  centralHi := (277924236482339014707/50000000000000000000)
  directionLo := (558085296782709336641/100000000000000000000)
  directionHi := (279042648391354668321/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree126.table
  base := (7502654979637622855476838312137917161467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-148522482913977383539920973244462903312500000000)
      constant := (5056168037481232126240802350833236564263591757923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree126.table
  base := (12004247967365972720720436307461157611401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1188490734426454435502096453389481039000000000000)
      constant := (40470068324291483528034750176041139352565372433845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558085296782709336641/100000000000000000000)
  centralHi := (279042648391354668321/50000000000000000000)
  directionLo := (56031319105739882477/10000000000000000000)
  directionHi := (560313191057398824771/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree127.table
  base := (30862099883000237261120585401823353643849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-598802293652189364411018021749017853875000000000)
      constant := (20552080517463471854057710671831547776833511400481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree127.table
  base := (61724199765770554460879976774427414798937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-10781261330850743675984505874631591526000000000000)
      constant := (370126937023055313028258952715878837438699440463177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56031319105739882477/10000000000000000000)
  centralHi := (560313191057398824771/100000000000000000000)
  directionLo := (22501290475376934751/4000000000000000000)
  directionHi := (70316532735552921097/12500000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree128.table
  base := (63448481111527173397310513633643635101187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1207029311296938389324704301040368189000000000000)
      constant := (41764262697736428853770241013073058750807140020603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree128.table
  base := (12689696222266440794747464069431990281601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-10866106051863397432450143668757853701000000000000)
      constant := (376070846960562670938613199689620841165722248775605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22501290475376934751/4000000000000000000)
  centralHi := (70316532735552921097/12500000000000000000)
  directionLo := (564742613275008524481/100000000000000000000)
  directionHi := (282371306637504262241/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree129.table
  base := (32597041936757315798722721364185539572233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-608227017644749024913686279291350335125000000000)
      constant := (21214824644137977758449826529974936056226350737377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree129.table
  base := (65194083873349309967534989163062623185301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1216772308097339020990642384764901764000000000000)
      constant := (42451371636791592626056740254270809936012180475869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564742613275008524481/100000000000000000000)
  centralHi := (282371306637504262241/50000000000000000000)
  directionLo := (566944347212816112211/100000000000000000000)
  directionHi := (141736086803204028053/25000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree130.table
  base := (16740252012955963615203557606571131457143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-306469689820514427582510204031258287875000000000)
      constant := (10775080201635888877400505592761022631290298637167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree130.table
  base := (13392201610336736136112593621927219455211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-11035795493888704945381419257010378051000000000000)
      constant := (388101430334722689747649346625458281123364406079655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566944347212816112211/100000000000000000000)
  centralHi := (141736086803204028053/25000000000000000000)
  directionLo := (284568781854425552633/50000000000000000000)
  directionHi := (569137563708851105267/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree131.table
  base := (68749253646338917757186243070296541138227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1235303483274617370832709073667365632750000000000)
      constant := (43776277252537587325186088264794267875499934180363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree131.table
  base := (4296828352888754593288707886019481337007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1390080026862669837730882131392080028250000000000)
      constant := (49273512971417881572903336660694984699016696335294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284568781854425552633/50000000000000000000)
  centralHi := (569137563708851105267/100000000000000000000)
  directionLo := (285661180427235732563/50000000000000000000)
  directionHi := (571322360854471465127/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree132.table
  base := (4409926291060205066362723479710703684237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-155591025908397128916922166401212264250000000000)
      constant := (5557189828282085491865243377815794228508562112106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree132.table
  base := (70558820656862526575637092951661182408063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1245053881768223606479188316140322489000000000000)
      constant := (44480262782330354735546211896627518496637999042647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285661180427235732563/50000000000000000000)
  centralHi := (571322360854471465127/100000000000000000000)
  directionLo := (573498834872580422777/100000000000000000000)
  directionHi := (286749417436290211389/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree133.table
  base := (72389709083616686818082158189357617513051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1254152931259736691838045588752030595250000000000)
      constant := (45144044927699708878244841149594050535039349365619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree133.table
  base := (72389709083531273486730733184876511221571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-11290329656926666214778332639389164576000000000000)
      constant := (406504214143602944300910895736459556048375576249491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573498834872580422777/100000000000000000000)
  centralHi := (286749417436290211389/50000000000000000000)
  directionLo := (287833540083538399001/50000000000000000000)
  directionHi := (575667080167076798003/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree134.table
  base := (7424191892623255214970940200264869822511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-631788827626148176170356923147181538250000000000)
      constant := (22917928078432859665186839147228924502670653821795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree134.table
  base := (2969676757046405927026018840234185854833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-11375174377939319971243970433515426751000000000000)
      constant := (412733651079223875324129265419200516297415068024825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287833540083538399001/50000000000000000000)
  centralHi := (575667080167076798003/100000000000000000000)
  directionLo := (577827189370635260861/100000000000000000000)
  directionHi := (288913594685317630431/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree135.table
  base := (76115450184755775226669970562515461504431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1273002379244856012843382103836695557750000000000)
      constant := (46532952313753935040083232018939228627320424708839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree135.table
  base := (38057725092347201280589254447342434737567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-636667727719554095983867123757871607000000000000)
      constant := (23278370880434944917268266026092394304567919368823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577827189370635260861/100000000000000000000)
  centralHi := (288913594685317630431/50000000000000000000)
  directionLo := (28998962669544247901/5000000000000000000)
  directionHi := (579979253390884958021/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree136.table
  base := (78010302859140890394861876960288859205887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1282427103237415673346050361379028039000000000000)
      constant := (47235333398363712206027722645175648114172565714903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree136.table
  base := (780103028590888711838461042380938297953/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-2886215954991156871043811505441987775250000000000)
      constant := (106333822112353146976539526119313557248957037662825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28998962669544247901/5000000000000000000)
  centralHi := (579979253390884958021/100000000000000000000)
  directionLo := (291061680727525819029/50000000000000000000)
  directionHi := (582123361455051638059/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree137.table
  base := (39963238474675258358133843184545656197343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-645925913614987666924359309460680260125000000000)
      constant := (23971499705347260753903722385536017602935117980967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree137.table
  base := (39963238474653213917574152118433927393363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-5814854270488640620320441907947106638000000000000)
      constant := (215853744441984941044818189560604456402576246025123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291061680727525819029/50000000000000000000)
  centralHi := (582123361455051638059/100000000000000000000)
  directionLo := (292129800576562651221/50000000000000000000)
  directionHi := (584259601153125302443/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree138.table
  base := (81863972455354053348273058905224233806391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1301276551222534994351386876463693001500000000000)
      constant := (48655950350745929632319436942051777561687759840079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree138.table
  base := (81863972455316687807183908132274484760349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1301617029109992777456280178891163939000000000000)
      constant := (48680808572388557643097060295456436690594466338981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292129800576562651221/50000000000000000000)
  centralHi := (584259601153125302443/100000000000000000000)
  directionLo := (293194029239806235571/50000000000000000000)
  directionHi := (586388058479612471143/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree139.table
  base := (2095569734428164564482833621409206243821/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-163837659401886831856756891750753185343750000000)
      constant := (6171773277314697967569606307970328933528326266245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree139.table
  base := (16764557875418983352601025127824980436503/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-11799397983002588753572159404146737626000000000000)
      constant := (444594653251990845819348042199417794547740931205315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293194029239806235571/50000000000000000000)
  centralHi := (586388058479612471143/100000000000000000000)
  directionLo := (117701763574785874727/20000000000000000000)
  directionHi := (147127204468482343409/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree140.table
  base := (85802927714647947554552816091211649064401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1320125999207654315356723391548357964000000000000)
      constant := (50097707014009198408048702958627168903645610043769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree140.table
  base := (42901463857310556708530469254618609830213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-5942121352007621255018898599136499900500000000000)
      constant := (225554808592724407094903650326745725294167896473973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117701763574785874727/20000000000000000000)
  centralHi := (147127204468482343409/25000000000000000000)
  directionLo := (590621962259489747367/100000000000000000000)
  directionHi := (73827745282436218421/12500000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree141.table
  base := (87804387467901976955681927853699935583371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1329550723200213975859391649090690445250000000000)
      constant := (50826512737220544646194778478586594429141834449699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree141.table
  base := (10975548433484904802770974423150803924983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-166237325347609670368103263783323083000000000000)
      constant := (6356557902109289997506255544029994302579247602127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590621962259489747367/100000000000000000000)
  centralHi := (73827745282436218421/12500000000000000000)
  directionLo := (296363786540769218847/50000000000000000000)
  directionHi := (118545514616307687539/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree142.table
  base := (4491358431843791664979247235344235830089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442016608334660246401592863587500000000000)
      linear := (-66404257448560485834262046549941625000000000)
      constant := (2557062258884717351421574269157628940671100005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree142.table
  base := (89827168636856566240261662289573594238139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (4449456)
      previous := (2224728)
      next := (2224728)
      square := (15912597900047768870457343089150000000000000)
      linear := (-2391178763348651065853813288340711000000000000)
      constant := (92101231611039361426175543317583647035934392059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296363786540769218847/50000000000000000000)
  centralHi := (118545514616307687539/20000000000000000000)
  directionLo := (594825730343779637383/100000000000000000000)
  directionHi := (74353216292972454673/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree143.table
  base := (22967817805389866305799643827827191328779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-337100042796333324216182041043838851937500000000)
      constant := (13074994741700436040664645412421931198868267078651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree143.table
  base := (45935635610771570229936703046625063123991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-6069388433526601889717355290325893163000000000000)
      constant := (235470017991794584358143758282153818565554924630311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594825730343779637383/100000000000000000000)
  centralHi := (74353216292972454673/12500000000000000000)
  directionLo := (298458256321923186017/50000000000000000000)
  directionHi := (119383302528769274407/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree144.table
  base := (46968347610972573618544732098727015404171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-678912447588946478683698210858843944500000000000)
      constant := (26522319736585672858870334355040514493488664664899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree144.table
  base := (93936695221931316124120877427025525122567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1358180176451761948433372041642005389000000000000)
      constant := (53071705694320794315147462970878181119049294433823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298458256321923186017/50000000000000000000)
  centralHi := (119383302528769274407/20000000000000000000)
  directionLo := (119799999441531144577/20000000000000000000)
  directionHi := (299499998603827861443/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree145.table
  base := (96023440638027093051296102308167046852981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1367249619170452617870064679260020370250000000000)
      constant := (53794584907260163404467146772730018793473816613789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree145.table
  base := (3000732519937980476306916547251884741723/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1538558288634813911545748271113038834500000000000)
      constant := (60549781793392829074997058818284248711798110122732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119799999441531144577/20000000000000000000)
  centralHi := (299499998603827861443/50000000000000000000)
  directionLo := (601076259922692273597/100000000000000000000)
  directionHi := (300538129961346136799/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree146.table
  base := (6133219216862570673887569077269065211731/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-172084292895376534796591617100294106437500000000)
      constant := (6818726908633517268532618167886448472970732235078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree146.table
  base := (24532876867447800962292192823700573749371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (5607426924)
      previous := (2803713462)
      next := (2803713462)
      square := (20053851503535200718993866628101287500000000000)
      linear := (-3098327757522791262207905990757643212750000000000)
      constant := (122799686319588773929357663385160408078692513033291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601076259922692273597/100000000000000000000)
  centralHi := (300538129961346136799/50000000000000000000)
  directionLo := (603145375370260366201/100000000000000000000)
  directionHi := (301572687685130183101/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree147.table
  base := (20052179143452886040916002085758393723919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1386099067155571938875401194344685332750000000000)
      constant := (55310330558595229872654577968480007594613349411555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree147.table
  base := (100260895717256020835976871441075693494123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1386461750122646533921917973017426114000000000000)
      constant := (55338536004724909306641944562485470785293982186787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603145375370260366201/100000000000000000000)
  centralHi := (301572687685130183101/50000000000000000000)
  directionLo := (605207416856743947537/100000000000000000000)
  directionHi := (302603708428371973769/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree148.table
  base := (51205802690207636887003704493181025546767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-697761895574065799689034725943508907000000000000)
      constant := (28038065387920707128464357925493785463148038123623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree148.table
  base := (102411605380408150304021516157020782528441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-12563000472116472561762899551283097201000000000000)
      constant := (504942490639649683147998290850690240177034746798761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605207416856743947537/100000000000000000000)
  centralHi := (302603708428371973769/50000000000000000000)
  directionLo := (60726245644391107553/10000000000000000000)
  directionHi := (607262456443911075531/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree149.table
  base := (13072954557406608057272767596342600081539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-175618564392586407485092213678668786906250000000)
      constant := (7105901990100835001871409513020030953724904457591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree149.table
  base := (13072954557405853816502771779458775692707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1580980649141140789778567168176169922000000000000)
      constant := (63985718133716437100896806742612594490717033687347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60726245644391107553/10000000000000000000)
  centralHi := (607262456443911075531/100000000000000000000)
  directionLo := (152327641244574632319/25000000000000000000)
  directionHi := (609310564978298529277/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree150.table
  base := (13347123619222145565093215910393105218413/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-176796654891656365047925745871460347062500000000)
      constant := (7202948249186378326553630653484049851620478741797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree150.table
  base := (26694247238443013430348714610638971371409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-353685830948382779852615976098211709750000000000)
      constant := (14413238537021378437317849593155433026355313208121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152327641244574632319/25000000000000000000)
  centralHi := (609310564978298529277/100000000000000000000)
  directionLo := (611351812119710423211/100000000000000000000)
  directionHi := (152837953029927605803/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree151.table
  base := (108991662863988760330865839818723093969083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1423797963125810580886074224514015257750000000000)
      constant := (58405240993894462352388533836999782057359783555027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree151.table
  base := (54495831431992215811001070835491208624257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-6408767317577216915579906466830941863000000000000)
      constant := (262957508714382070959567821459635423767516129574897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611351812119710423211/100000000000000000000)
  centralHi := (152837953029927605803/25000000000000000000)
  directionLo := (306693133184431629519/50000000000000000000)
  directionHi := (613386266368863259039/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree152.table
  base := (111227658189888749054049899583771826216631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1433222687118370241388742482056347739000000000000)
      constant := (59192180922017002770898747986577736394666125570639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree152.table
  base := (111227658189885082915406039618040724692703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-12902379356167087587625450727788145901000000000000)
      constant := (533001035357715193900733404574189674296780327921263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306693133184431629519/50000000000000000000)
  centralHi := (613386266368863259039/100000000000000000000)
  directionLo := (153853498773552113781/25000000000000000000)
  directionHi := (4923311960753667641/800000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree153.table
  base := (5674248746573932186887096430734503265847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-360661852777732475472852684899670055062500000000)
      constant := (14996101444464667323241800011670349049047149115715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree153.table
  base := (113484974931475538887892985741724774488689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1443024897464415704899009835768267564000000000000)
      constant := (60014960124402552759743255537767123328371724828441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153853498773552113781/25000000000000000000)
  centralHi := (4923311960753667641/800000000000000000)
  directionLo := (617435064557962067927/100000000000000000000)
  directionHi := (77179383069745258491/12500000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree154.table
  base := (1447045163609503673236573398814650240879/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-181509016887936195299259874642626587687500000000)
      constant := (7597739445177436013437568036088521922691592235510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree154.table
  base := (115763613088757664476385762421417167666427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-13072068798192395100556726316040670251000000000000)
      constant := (547315834714487722400401337162394672226921477515467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617435064557962067927/100000000000000000000)
  centralHi := (77179383069745258491/12500000000000000000)
  directionLo := (61944953994137015957/10000000000000000000)
  directionHi := (619449539941370159571/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree155.table
  base := (1180635726617358188667752281624176504411/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-365374214774012305724186813670836295687500000000)
      constant := (15396177568174872306564316091168326733642772011475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree155.table
  base := (7378973291358349514610908322753876380727/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159301901250000000000000000000000000000000000000
      center := (2803713462)
      previous := (1401856731)
      next := (1401856731)
      square := (10026925751767600359496933314050643750000000000)
      linear := (-1644614189900631107127795513770866553250000000000)
      constant := (69318077017788713545581681490615626694289772931534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61944953994137015957/10000000000000000000)
  centralHi := (619449539941370159571/100000000000000000000)
  directionLo := (621457485369237066619/100000000000000000000)
  directionHi := (31072874268461853331/5000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree156.table
  base := (24076970730081510529057767096039774326249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1470921583088608883399415512225677664000000000000)
      constant := (62392789911698705697429210217788238988032734880405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree156.table
  base := (120384853650405667150061118060477502713167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1471306471135300290387555767143688289000000000000)
      constant := (62424553933676581286615356208070817668116403245223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621457485369237066619/100000000000000000000)
  centralHi := (31072874268461853331/5000000000000000000)
  directionLo := (31172948196687134199/5000000000000000000)
  directionHi := (623458963933742683981/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree157.table
  base := (1534093200684724964382027255904272669793/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-185043288385146067987760471221001268156250000000)
      constant := (7900769309802146618642190564830248411231274187670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree157.table
  base := (61363728027388200296844615863463706133807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-6663301480615178184976819849209728388000000000000)
      constant := (284572471248413306048834928699559149480551893600447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31172948196687134199/5000000000000000000)
  centralHi := (623458963933742683981/100000000000000000000)
  directionLo := (62545403771757379141/10000000000000000000)
  directionHi := (625454037717573791411/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree158.table
  base := (6254568993742489187736433545786962684877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-372442757768432051101188006827585656625000000000)
      constant := (16006200993213732060514079552975316965721197821065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree158.table
  base := (62545689937424215956674229529103907312193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-6705723841121505063209638746272859475500000000000)
      constant := (288258243711761093140829928280109634381408897765553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62545403771757379141/10000000000000000000)
  centralHi := (625454037717573791411/100000000000000000000)
  directionLo := (125488553563278683121/20000000000000000000)
  directionHi := (313721383908196707803/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree159.table
  base := (31869156277656410265491735204099964721917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (793238064298690744788333793287500000000000)
      linear := (-133427888489345662594110028911772437500000000)
      constant := (5771514631097544518839613284200810826460058597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree159.table
  base := (31869156277656124118163265333696491294841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (793238064298690744788333793287500000000000)
      linear := (-133462802136541907785341909800561500000000000)
      constant := (5774451368450380747699929718670290168867293481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125488553563278683121/20000000000000000000)
  centralHi := (313721383908196707803/50000000000000000000)
  directionLo := (629425214360671235291/100000000000000000000)
  directionHi := (157356303590167808823/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree160.table
  base := (64941595881054184079146337586479178977299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-754310239529423762705044271197503794500000000000)
      constant := (32838978872444229249772641051505273784299801003531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree160.table
  base := (64941595881053699542679584316314004706237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-6790568562134158819675276540399121650500000000000)
      constant := (295701170387894659446822284635429366453364001466477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629425214360671235291/100000000000000000000)
  centralHi := (157356303590167808823/25000000000000000000)
  directionLo := (39462589783556068601/6250000000000000000)
  directionHi := (631401436536897097617/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree161.table
  base := (26462215965860162484402594733822116771131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1518045203051407185912756799937340070250000000000)
      constant := (66512462022484313419004515402512958769639433905695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree161.table
  base := (132311079829299991983043501974690806535587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-13665981845280971395816190874924505476000000000000)
      constant := (598916649201361598264100867315710496428736947907827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39462589783556068601/6250000000000000000)
  centralHi := (631401436536897097617/100000000000000000000)
  directionLo := (316685746304099409497/50000000000000000000)
  directionHi := (126674298521639763799/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree162.table
  base := (134760289312205851160662078640144023843241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1527469927043966846415425057479672551500000000000)
      constant := (67352251227799615715220544604542169532304072067729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree162.table
  base := (33690072328051289146335887002557675872261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (623047436)
      previous := (311523718)
      next := (311523718)
      square := (2228205722615022302110429625344587500000000000)
      linear := (-381967404619267365341161907473632434750000000000)
      constant := (16846626262774819668174384099238003777098438172109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316685746304099409497/50000000000000000000)
  centralHi := (126674298521639763799/20000000000000000000)
  directionLo := (635335439934384590041/100000000000000000000)
  directionHi := (317667719967192295021/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree163.table
  base := (68615410105413188228559616163801289869201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-768447325518263253459046657511002516375000000000)
      constant := (34098662680417203170287850892915190163649467804969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree163.table
  base := (27446164042165157691818492817419427159489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-13835671287306278908747466463177029826000000000000)
      constant := (614088029551385417279616824767073909689394938713845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635335439934384590041/100000000000000000000)
  centralHi := (317667719967192295021/50000000000000000000)
  directionLo := (79661666873928686267/12500000000000000000)
  directionHi := (637293334991429490137/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree164.table
  base := (69861336262582641352966234286640480564663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-773159687514543083710380786282168757000000000000)
      constant := (34523842210794363140092969892097561752849343508047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree164.table
  base := (27944534505032956990090897938013997847483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-13920516008318932665213104257303292001000000000000)
      constant := (621745101475837695182319893094976422563869797708215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79661666873928686267/12500000000000000000)
  centralHi := (637293334991429490137/100000000000000000000)
  directionLo := (319622616695212420263/50000000000000000000)
  directionHi := (639245233390424840527/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree165.table
  base := (142235846255225456403581034798677894443653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1555744099021645827923429830106669995250000000000)
      constant := (69903328410062616407329222648117635267003474957357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree165.table
  base := (17779480781903129382051030888416392671999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17700211250000000000000000000000000000000000000
      center := (311523718)
      previous := (155761859)
      next := (155761859)
      square := (1114102861307511151055214812672293750000000000)
      linear := (-194518899018494255856649195158743808000000000000)
      constant := (8742357794906259860285502119238417686121492407831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319622616695212420263/50000000000000000000)
  centralHi := (639245233390424840527/100000000000000000000)
  directionLo := (12823823797920167673/2000000000000000000)
  directionHi := (641191189896008383651/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree166.table
  base := (72385170700504883912990744106954294349401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-782584411507102744213049043824501238250000000000)
      constant := (35382128663128058682798802728795657740185138208769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree166.table
  base := (144770341401009411171101075754474297472379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-14090205450344240178144379845555816351000000000000)
      constant := (637202008823624827616604651670869375116286435248459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12823823797920167673/2000000000000000000)
  centralHi := (641191189896008383651/100000000000000000000)
  directionLo := (160782814611073142207/25000000000000000000)
  directionHi := (643131258444292568829/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree167.table
  base := (147326157962521064285062875123075022379283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1574593547006765148928766345191334957750000000000)
      constant := (71630471170169269473409199224291073554374116878827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree167.table
  base := (147326157962520762400781349326475711459131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (22429707696)
      previous := (11214853848)
      next := (11214853848)
      square := (80215406014140802875975466512405150000000000000)
      linear := (-14175050171356893934610017639682078526000000000000)
      constant := (645001844246960411304899173699550491570533783978251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160782814611073142207/25000000000000000000)
  centralHi := (643131258444292568829/100000000000000000000)
  directionLo := (645065492160307548799/100000000000000000000)
  directionHi := (201582966300096109/31250000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree168.table
  base := (149903295939762164705458650223768703817909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2492189744)
      previous := (1246094872)
      next := (1246094872)
      square := (8912822890460089208441718501378350000000000000)
      linear := (-1584018270999324809431434602733667439000000000000)
      constant := (72501969941802112647213211929788649139972536666621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree168.table
  base := (74951647969880954594976187344098881267299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-792216382909419316170869746322685594500000000000)
      constant := (36269403750180990024843173121533179212455888013531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell159.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645065492160307548799/100000000000000000000)
  centralHi := (201582966300096109/31250000000000000)
  directionLo := (646993943374974846281/100000000000000000000)
  directionHi := (323496971687487423141/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 31833
  qDenominator := 60208
  table := BinomialMassData.Q31833_60208.Degree169.table
  base := (76250877666367927651881373883015438700897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1246094872)
      previous := (623047436)
      next := (623047436)
      square := (4456411445230044604220859250689175000000000000)
      linear := (-796721497495942234967051430137999960125000000000)
      constant := (36689376820577343170153742143719757257328685721593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31833_60208.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 23881
  qDenominator := 45156
  table := BinomialMassData.Q23881_45156.Degree169.table
  base := (15250175533273563904254889084373151605899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (11214853848)
      previous := (5607426924)
      next := (5607426924)
      square := (40107703007070401437987733256202575000000000000)
      linear := (-7172369806691100723770646613967301438000000000000)
      constant := (330372139296258705143589857879214484234659305661895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23881_45156.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell159.Kernel169
