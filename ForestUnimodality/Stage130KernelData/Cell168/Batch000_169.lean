import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell168.Parameters
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch000_049
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch050_099
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch100_149
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch150_199
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree000.table
  base := (35176770607326934188648693/400000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78620777578963397386191402500000000000)
      linear := (-6016425463425864031061229875000000000)
      constant := (109927408147896669339527165625000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree000.table
  base := (35176770607326934188648693/400000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78620777578963397386191402500000000000)
      linear := (-6016425463425864031061229875000000000)
      constant := (109927408147896669339527165625000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree001.table
  base := (244671768580153523145504351515809588405181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-95346581751286378427572530257571000000000000)
      constant := (65396616989511333461986122676419169756727423313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree001.table
  base := (244620880951361912867368582257779094118707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-858328563581881395893693506927295250000000000)
      constant := (588447309487550205181589750543967612380858247799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49914248785049739213/100000000000000000000)
  directionHi := (24957124392524869607/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree002.table
  base := (35949486387861483848343410216379071103953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-46065864435303310843015543159392125000000000)
      constant := (9629957606718669783906066262256870126556434869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree002.table
  base := (287490866966300940631452540655271798112801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-3317579550623054340879282045912858000000000000)
      constant := (693105329411249730931309407772354399742222434157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49914248785049739213/100000000000000000000)
  centralHi := (24957124392524869607/50000000000000000000)
  directionLo := (35294703793741061563/50000000000000000000)
  directionHi := (70589407587482123127/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree003.table
  base := (180708643758692274196400969635820638482227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-546360667462280216633103630035132000000000000)
      constant := (48724322623414519070704000635585849382712034271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree003.table
  base := (90312765412482174619440487880612011647223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-273250109671241438331732059887284750000000000)
      constant := (24351171992180687356837885465199725714386010579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35294703793741061563/50000000000000000000)
  centralHi := (70589407587482123127/100000000000000000000)
  directionLo := (10806751864667406637/12500000000000000000)
  directionHi := (86454014917339253097/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree004.table
  base := (122001932168934388728675765548320594457187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-724194419442133946522082914795127000000000000)
      constant := (33375620261733658742935264783447843682910022351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree004.table
  base := (121941497988333284960290184748529527184023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-6519424397541637439063072110029393000000000000)
      constant := (300238873849924829852958299664800583797032792811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10806751864667406637/12500000000000000000)
  centralHi := (86454014917339253097/100000000000000000000)
  directionLo := (49914248785049739213/50000000000000000000)
  directionHi := (99828497570099478427/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree005.table
  base := (22024359421446498255745249395498783405931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-225507042855496919102765549888780500000000000)
      constant := (6186874560152374802592307740424778255787803063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree005.table
  base := (88054297371806293833294088355599975785057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-8120346821000928988154967142087660500000000000)
      constant := (222629369745491084885505308054963902926914304749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49914248785049739213/50000000000000000000)
  centralHi := (99828497570099478427/100000000000000000000)
  directionLo := (111611653329207505453/100000000000000000000)
  directionHi := (55805826664603752727/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree006.table
  base := (8404008023265435636801631377280649610779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-134982740425230175787505185539389625000000000)
      constant := (2462146859942342294986655714390923873460657767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree006.table
  base := (13440143897916150076009393944471525923879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-1080141027162246726360762463793992000000000000)
      constant := (19689697314933114867732300016463007915802620335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111611653329207505453/100000000000000000000)
  centralHi := (55805826664603752727/50000000000000000000)
  directionLo := (61132220208853522799/50000000000000000000)
  directionHi := (122264440417707045599/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree007.table
  base := (53442131889085449651190763727716965491803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-1257695675381695136189020769075112000000000000)
      constant := (16631315960429289283756260614146829758841482919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree007.table
  base := (53418473644730766566947580690628936888701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-11322191667919512086338757206204195500000000000)
      constant := (149635924285317654072802359476936767551409210457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61132220208853522799/50000000000000000000)
  centralHi := (122264440417707045599/100000000000000000000)
  directionLo := (66030344581924747763/50000000000000000000)
  directionHi := (132060689163849495527/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree008.table
  base := (5458360324774579047297584328116295624511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-179441178420193608259750006729388375000000000)
      constant := (1841521191706783607609319757520807675887477403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree008.table
  base := (174592787279760850645482698255280852607/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-6461557045689401817715326119131231500000000000)
      constant := (66279451169710662356824060360125885887766262375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66030344581924747763/50000000000000000000)
  centralHi := (132060689163849495527/100000000000000000000)
  directionLo := (35294703793741061563/25000000000000000000)
  directionHi := (141178815174964246253/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree009.table
  base := (36304904078218892239232744095926391305007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-1613363179341402595966979338595102000000000000)
      constant := (13571881488088397236036519719406016931632635211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree009.table
  base := (4536188810444196000524238321438065873789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-201722729372751322007257600976676812500000000)
      constant := (1696222341607875582535982443110675180338453497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35294703793741061563/25000000000000000000)
  centralHi := (141178815174964246253/100000000000000000000)
  directionLo := (149742746355149217639/100000000000000000000)
  directionHi := (3743568658878730441/2500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree010.table
  base := (30493599125515138514896821407243437440003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-1791196931321256325855958623355097000000000000)
      constant := (12919989141044341970614794269954358411157921519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree010.table
  base := (6096098635230328108124087899029724690337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-16124958938297386733614442302378998000000000000)
      constant := (116270703775658171569924086516402623248613328545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149742746355149217639/100000000000000000000)
  centralHi := (3743568658878730441/2500000000000000000)
  directionLo := (15784271385704946017/10000000000000000000)
  directionHi := (157842713857049460171/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree011.table
  base := (25748676907011373342309669326403585732309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-1969030683301110055744937908115092000000000000)
      constant := (12647103057777223833541187430698663148358192457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree011.table
  base := (12868632754537872680315708068169031170003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-8862940680878339141353168667218632750000000000)
      constant := (56911736153969876092233979674552985747111403671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784271385704946017/10000000000000000000)
  centralHi := (157842713857049460171/100000000000000000000)
  directionLo := (5173338591014464467/3125000000000000000)
  directionHi := (33109366982492572589/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree012.table
  base := (21783058254941759145273293202338291636121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-2146864435280963785633917192875087000000000000)
      constant := (12676523435797540702070152376728994891297355933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree012.table
  base := (21772987169031142174476323667974164280421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-2147422642801774425755359151832837000000000000)
      constant := (12677398923266302551035636725565415393292919833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5173338591014464467/3125000000000000000)
  centralHi := (33109366982492572589/20000000000000000000)
  directionLo := (172908029834678506193/100000000000000000000)
  directionHi := (86454014917339253097/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree013.table
  base := (4603827773182187676221554836594529967459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-581174546815204378880724119408770500000000000)
      constant := (3239944130727460021858031419555618651870923407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree013.table
  base := (1840635995068481333157187122636792512247/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-10463863104337630690445063699276900250000000000)
      constant := (58327057955654069485824396965015741815918047895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172908029834678506193/100000000000000000000)
  centralHi := (86454014917339253097/50000000000000000000)
  directionLo := (11248023960672685323/6250000000000000000)
  directionHi := (179968383370762965169/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree014.table
  base := (7761431437071616071556667860639733608473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-1251265969620335622705937881197538500000000000)
      constant := (6732057122110225206572416173426308547376556829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree014.table
  base := (969680275785048213577778967305145199747/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-2816081079016819116247752803826508500000000000)
      constant := (15150186528022103043948356646483176731823594158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11248023960672685323/6250000000000000000)
  centralHi := (179968383370762965169/100000000000000000000)
  directionLo := (186762017671853585969/100000000000000000000)
  directionHi := (18676201767185358597/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree015.table
  base := (13017690514695401803462131650234079608759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-2680365691220524975300855047155072000000000000)
      constant := (14166019208176977901238198827564530688810968307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree015.table
  base := (6505288400640681677107274393979903091571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-1340531725310769137726328747926129750000000000)
      constant := (7084842072107348319366156745725966437746798783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186762017671853585969/100000000000000000000)
  centralHi := (18676201767185358597/10000000000000000000)
  directionLo := (193317054282951431763/100000000000000000000)
  directionHi := (48329263570737857941/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree016.table
  base := (5416681194728483460359499590555783184267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-1429099721600189352594917165957533500000000000)
      constant := (7523871339126227894375904921481841260690167191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree016.table
  base := (5413513378836811400875630568079691351247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-12865246739526568014082906247364301500000000000)
      constant := (67735711819276302368645954835455114896480432579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193317054282951431763/100000000000000000000)
  centralHi := (48329263570737857941/25000000000000000000)
  directionLo := (49914248785049739213/25000000000000000000)
  directionHi := (199656995140198956853/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree017.table
  base := (1783574038795068908702335074853294700451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-3036033195180232435078813616675062000000000000)
      constant := (16095389439721374130818683786676177712517975115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree017.table
  base := (8912237970292124216180600844365030492639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-27331415902512427577257707526786870500000000000)
      constant := (144909263151377551208669996273786844454413555923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49914248785049739213/25000000000000000000)
  centralHi := (199656995140198956853/100000000000000000000)
  directionLo := (102900859982059029001/50000000000000000000)
  directionHi := (205801719964118058003/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree018.table
  base := (7229460200308876452966384020746442780777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-3213866947160086164967792901435057000000000000)
      constant := (17297804023828376276127657247627587857068533421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree018.table
  base := (7224464174271531307752700820608340465219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-3214704258441302125149955839871682000000000000)
      constant := (17304477173666812303317001118514995334613955887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102900859982059029001/50000000000000000000)
  centralHi := (205801719964118058003/100000000000000000000)
  directionLo := (105884111381223184689/50000000000000000000)
  directionHi := (211768222762446369379/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree019.table
  base := (2867028014195723856613413572792314775327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-1695850349569969947428386093097526000000000000)
      constant := (9322941070941029049460597763476048084218440571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree019.table
  base := (5729634377327665852610869155861597123669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-30533260749431010675441497590903405500000000000)
      constant := (167882592230430016563418775522758613973023159633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105884111381223184689/50000000000000000000)
  centralHi := (211768222762446369379/100000000000000000000)
  directionLo := (13598197893548728541/6250000000000000000)
  directionHi := (217571166296779656657/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree020.table
  base := (4403556066846054024193894079606098919149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-3569534451119793624745751470955047000000000000)
      constant := (20132115802065991229328918929834227766525795777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree020.table
  base := (2199825741897271021205439017199944837733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-16067091586445151112266696311480836500000000000)
      constant := (90634297542800176436006260619130884009184749281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13598197893548728541/6250000000000000000)
  centralHi := (217571166296779656657/100000000000000000000)
  directionLo := (111611653329207505453/50000000000000000000)
  directionHi := (223223306658415010907/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree021.table
  base := (200914697740435237259947793688784945949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-468421025387455919329341344464380250000000000)
      constant := (2718784144198929935166707465817569879165564354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree021.table
  base := (3211194527625662148819181104319843579249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-3748345066261065974847254183891104500000000000)
      constant := (21760247392928716801942857777538966396723693077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111611653329207505453/50000000000000000000)
  centralHi := (223223306658415010907/100000000000000000000)
  directionLo := (114367911657174000693/50000000000000000000)
  directionHi := (228735823314348001387/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree022.table
  base := (8591419465795981752338602064344511003/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-1962600977539750542261855020237518500000000000)
      constant := (11747580383334839926856512709417814004775564875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree022.table
  base := (428965823888232341319658042544191348921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-35336028019808885322717182687078208000000000000)
      constant := (211556755485680232840900313001051430024437164985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114367911657174000693/50000000000000000000)
  centralHi := (228735823314348001387/100000000000000000000)
  directionLo := (234118579141144768047/100000000000000000000)
  directionHi := (14632411196321548003/6250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree023.table
  base := (237395057706867809009685058166738706703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-4103035707059354814412689325235032000000000000)
      constant := (25362439782206958720739310207408167339929803095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree023.table
  base := (1184319363475106049774698336522233166693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (28535568463839923008112941920180000000000000)
      linear := (-696923593269210884373756183379933500000000000)
      constant := (4308927203712272626031076266433309337164694717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234118579141144768047/100000000000000000000)
  centralHi := (14632411196321548003/6250000000000000000)
  directionLo := (2992254097322689393/1250000000000000000)
  directionHi := (239380327785815151441/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree024.table
  base := (31840745946729781019199245047738638051/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-2140434729519604272150834304997513500000000000)
      constant := (13674239797075812529716854493708628875719999115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree024.table
  base := (316080187972897489837513816711322090899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-4281985874080829824544552527910527000000000000)
      constant := (27362079932242897786625913693630314556991758527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2992254097322689393/1250000000000000000)
  centralHi := (239380327785815151441/100000000000000000000)
  directionLo := (244528880835414091197/100000000000000000000)
  directionHi := (122264440417707045599/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree025.table
  base := (-46923089615738987310983883683240914237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-2229351605509531137095323947377511000000000000)
      constant := (14725119582918414455284674824372570969852789995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree025.table
  base := (-58908364377868043949603745260536879123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-5017349411273344996249108472906626312500000000)
      constant := (33148265999378551299331750322026680170812261489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244528880835414091197/100000000000000000000)
  centralHi := (122264440417707045599/50000000000000000000)
  directionLo := (49914248785049739213/20000000000000000000)
  directionHi := (124785621962624348033/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree026.table
  base := (-74092506519338629978228302340236780021/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6301250000000000000000000000000000000000000
      center := (110902)
      previous := (55451)
      next := (55451)
      square := (396327339775554486223790860002500000000000)
      linear := (-10935228686318198122829309385648625000000000)
      constant := (74682003725830823582785704549997170283828278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree026.table
  base := (-148407334496655844685967088100267024879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-5217464714205756439885595351913909750000000000)
      constant := (35641554499911343081959795653381722809395526397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49914248785049739213/20000000000000000000)
  centralHi := (124785621962624348033/50000000000000000000)
  directionLo := (50902745712258714481/20000000000000000000)
  directionHi := (127256864280646786203/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree027.table
  base := (-919170168588416505275121611499124559473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-2407185357489384866984303232137506000000000000)
      constant := (16995566702946974528669049556572379362821920171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree027.table
  base := (-919945937972503365401804034062183824987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-2407813340950296837120925435964974750000000000)
      constant := (17004356371504498208346645567378175262489248249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50902745712258714481/20000000000000000000)
  centralHi := (127256864280646786203/50000000000000000000)
  directionLo := (259362044752017759289/100000000000000000000)
  directionHi := (25936204475201775929/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree028.table
  base := (-121726126055478027896064024140474607179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-1248051116739655865964396437258751750000000000)
      constant := (9106584416484044933726502692235402013880825165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree028.table
  base := (-608968569134836302964456294661284169297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-11235390640141158654317138219856953250000000000)
      constant := (82001983715821693278365161187963428771727713571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259362044752017759289/100000000000000000000)
  centralHi := (25936204475201775929/10000000000000000000)
  directionLo := (264121378327698991053/100000000000000000000)
  directionHi := (132060689163849495527/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree029.table
  base := (-2979657563355445456749185362920307502319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-5170038218938477193746565033795002000000000000)
      constant := (38969277933496832810424881052606857871182925813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree029.table
  base := (-2980833858578466674723082218392358126029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-46542484984023926166360447911486080500000000000)
      constant := (350907463727226263221778623539938966724675085847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264121378327698991053/100000000000000000000)
  centralHi := (132060689163849495527/50000000000000000000)
  directionLo := (268796455931806031033/100000000000000000000)
  directionHi := (134398227965903015517/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree030.table
  base := (-3478471153591524072224160760891280372901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-5347871970918330923635544318554997000000000000)
      constant := (41618691631887825447097747885390553948930921127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree030.table
  base := (-3479493627110231105690721121275467317781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-5349267489720357523939149215949372000000000000)
      constant := (41640627171561174556681867365609715507806496887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268796455931806031033/100000000000000000000)
  centralHi := (134398227965903015517/50000000000000000000)
  directionLo := (68347900001241433997/25000000000000000000)
  directionHi := (273391600004965735989/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree031.table
  base := (-39349299846512714577699066966608347379/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-1381426430724546163381130900828748000000000000)
      constant := (11093379741971189903619060265466421934517760825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree031.table
  base := (-1967908914486460985346168087088410607047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-24872164915471254632272118987801307750000000000)
      constant := (199786472528137487051272558219908077007513386821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68347900001241433997/25000000000000000000)
  centralHi := (273391600004965735989/100000000000000000000)
  directionLo := (55582155116566331421/20000000000000000000)
  directionHi := (138955387791415828553/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree032.table
  base := (-2176182083427124156528829856251790520619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-2851769737439019191706751444037493500000000000)
      constant := (23616435112961613660873548650661562371234659913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree032.table
  base := (-4353134359072668162922602083469637291807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-51345252254401800813636133007660883000000000000)
      constant := (425321363150907675925970046559992445362524435501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55582155116566331421/20000000000000000000)
  centralHi := (138955387791415828553/50000000000000000000)
  directionLo := (35294703793741061563/12500000000000000000)
  directionHi := (56471526069985698501/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree033.table
  base := (-4733569771415259705634625168944028048451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-5881373226857892113302482172834982000000000000)
      constant := (50195998371268555454598527105975450381711200977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree033.table
  base := (-4734237292351427230688382268720258561501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-5882908297540121373636447559968794500000000000)
      constant := (50222686701720940873769721118606014062473093327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35294703793741061563/12500000000000000000)
  centralHi := (56471526069985698501/20000000000000000000)
  directionLo := (71683882275150727879/25000000000000000000)
  directionHi := (286735529100602911517/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree034.table
  base := (-2540447382637200941301073717572165578623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-3029603489418872921595730728797488500000000000)
      constant := (26631138045274728839201861498340252055862557221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree034.table
  base := (-2540736402503134569967732375854383711473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-27273548550660191955909961535888709000000000000)
      constant := (239807877517809725975156370376956874009641617539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71683882275150727879/25000000000000000000)
  centralHi := (286735529100602911517/100000000000000000000)
  directionLo := (232838066826372411/80000000000000000)
  directionHi := (291047583532965513751/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree035.table
  base := (-5396311051348444241594989480287824094343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-6237040730817599573080440742354972000000000000)
      constant := (56431176544547951962888412446672667110742097661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree035.table
  base := (-5396811199913486600291531129547757748917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-56148019524779675460911818103835685500000000000)
      constant := (508151349605727318416141589441263042348662385231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232838066826372411/80000000000000000)
  centralHi := (291047583532965513751/100000000000000000000)
  directionLo := (295296678125837334739/100000000000000000000)
  directionHi := (14764833906291866737/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree036.table
  base := (-2840737438591674591374109989549399541787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-3207437241398726651484710013557483500000000000)
      constant := (29851128614319220447860654376459913026222141849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree036.table
  base := (-1420476824989826709695516403625751079793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-1604137276339971305833436475997054250000000000)
      constant := (14933527358607145260529981080236357081758464811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295296678125837334739/100000000000000000000)
  centralHi := (14764833906291866737/5000000000000000000)
  directionLo := (149742746355149217639/50000000000000000000)
  directionHi := (299485492710298435279/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree037.table
  base := (-5937777501740377259818510595523609371553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-6592708234777307032858399311874962000000000000)
      constant := (63075146435990467610973580676950441900874070331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree037.table
  base := (-1484537774885126272876215579655130311103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-14837466092924564639773902041988055125000000000)
      constant := (141994829656813114541935081394743039562806353629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149742746355149217639/50000000000000000000)
  centralHi := (299485492710298435279/100000000000000000000)
  directionLo := (303616522237683989621/100000000000000000000)
  directionHi := (151808261118841994811/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree038.table
  base := (-1233277539992855401459657452461393535513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-6770541986757160762747378596634957000000000000)
      constant := (66549531901495718808439283305035311524681926255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree038.table
  base := (-1541677563565264164282233365187475366307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-15237696698789387527046875800002622000000000000)
      constant := (149816385765864219187470736374683157904993939001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303616522237683989621/100000000000000000000)
  centralHi := (151808261118841994811/50000000000000000000)
  directionLo := (76923023539559458069/25000000000000000000)
  directionHi := (307692094158237832277/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree039.table
  base := (-6368287426530831385446105119981670676063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-6948375738737014492636357881394952000000000000)
      constant := (70125151273377601527277257684612866037964220101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree039.table
  base := (-254742629219185850281361515878065591619/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-6950189913179649073031044248007639500000000000)
      constant := (70162588825438438363102269981348668870384422825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76923023539559458069/25000000000000000000)
  centralHi := (307692094158237832277/100000000000000000000)
  directionLo := (155857191877097650439/50000000000000000000)
  directionHi := (311714383754195300879/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree040.table
  base := (-16360754361839031551341512469397240311/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-890776186339608527815667145769368375000000000)
      constant := (9225223014625030981134628650511499680719459850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree040.table
  base := (-3272270860417514542467514273303335813541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-32076315821038066603185646632063511500000000000)
      constant := (332285302952770398224759686493960229496199293663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155857191877097650439/50000000000000000000)
  centralHi := (311714383754195300879/100000000000000000000)
  directionLo := (15784271385704946017/5000000000000000000)
  directionHi := (315685427714098920341/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree041.table
  base := (-1339024789313305277353144760348529977511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-7304043242696721952414316450914942000000000000)
      constant := (77579245203463373051146646804442990189092267985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree041.table
  base := (-1673832687971768788553269292882847826433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-16438388516383856188865797074046322625000000000)
      constant := (174646449318413552233728496184500501348546994819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784271385704946017/5000000000000000000)
  centralHi := (315685427714098920341/100000000000000000000)
  directionLo := (319607136188805105429/100000000000000000000)
  directionHi := (31960713618880510543/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree042.table
  base := (-6821336639624313648161313510203036312439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-7481876994676575682303295735674937000000000000)
      constant := (81457378875746464367903897197090675679296735053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree042.table
  base := (-1705378689895247270715141074255883974531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-1870957680249853230682085648006765500000000000)
      constant := (20375207617642655259541065570655953007747629137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319607136188805105429/100000000000000000000)
  centralHi := (31960713618880510543/10000000000000000000)
  directionLo := (32348130353172693591/10000000000000000000)
  directionHi := (323481303531726935911/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree043.table
  base := (-1384685890158337420721938502388900931349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-7659710746656429412192275020434932000000000000)
      constant := (85436054318766386799449226036471272794843468115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree043.table
  base := (-865447847805114486128061784065653885603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-8619424864056750981705872295037728187500000000)
      constant := (96166807608622304387851499258409482280811732129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32348130353172693591/10000000000000000000)
  centralHi := (323481303531726935911/100000000000000000000)
  directionLo := (163654808947339745433/50000000000000000000)
  directionHi := (327309617894679490867/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree044.table
  base := (-7001813891323924582811063686127554300657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-7837544498636283142081254305194927000000000000)
      constant := (89515161587826534002188141018750833434830567339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree044.table
  base := (-700194581714449392230660594311987537979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-35278160667956649701369436696180046500000000000)
      constant := (403032884455122277087955788478434726908199148485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163654808947339745433/50000000000000000000)
  centralHi := (327309617894679490867/100000000000000000000)
  directionLo := (5173338591014464467/1562500000000000000)
  directionHi := (331093669824925725889/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree045.table
  base := (-7056835839953445524913788930646981559421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8015378250616136871970233589954922000000000000)
      constant := (93694608273468329277305056850583111183324813167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree045.table
  base := (-882118661628910726513019132922825221191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1002183941102397096553205117005810562500000000)
      constant := (11718063441033298553685021346056321901944361957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5173338591014464467/1562500000000000000)
  centralHi := (331093669824925725889/100000000000000000000)
  directionLo := (8370873999690562909/2500000000000000000)
  directionHi := (334834959987622516361/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree046.table
  base := (-1772196506712166703049699990303312919749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-2048303000648997650464803218678729250000000000)
      constant := (24493579175110121545277582540671648477291900423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree046.table
  base := (-1772220887083473598997308150412711702227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-18439541545707970625230665864119157000000000000)
      constant := (220559539816651921847434506293734616546803151561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8370873999690562909/2500000000000000000)
  centralHi := (334834959987622516361/100000000000000000000)
  directionLo := (338534906120016833469/100000000000000000000)
  directionHi := (33853490612001683347/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree047.table
  base := (-7097908839493778028357085377087113576131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8371045754575844331748192159474912000000000000)
      constant := (102354221575005691329960488458030989542024352337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree047.table
  base := (-3548996314569931777502272842767213650901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-37679544303145587025007279244267447750000000000)
      constant := (460838978312073501248596323719108621646792944143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338534906120016833469/100000000000000000000)
  centralHi := (33853490612001683347/10000000000000000000)
  directionLo := (34219484930878847209/10000000000000000000)
  directionHi := (342194849308788472091/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree048.table
  base := (-7084409719801240099825693584596240004399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8548879506555698061637171444234907000000000000)
      constant := (106834268008631866800756566202752514769304705973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree048.table
  base := (-7084481680334168116016715335177445129821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8551112336638940622122939280065907000000000000)
      constant := (106891051838271806752546608584049207452330333967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34219484930878847209/10000000000000000000)
  centralHi := (342194849308788472091/100000000000000000000)
  directionLo := (172908029834678506193/50000000000000000000)
  directionHi := (345816059669357012387/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree049.table
  base := (-7048461378396912148297539220599112264353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8726713258535551791526150728994902000000000000)
      constant := (111414409857702969934378502314577778566496015931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree049.table
  base := (-1409704630879870901986820146113665771821/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-78560933453209757148198348552651430500000000000)
      constant := (1003262274355681387818652803204859901691662058515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172908029834678506193/50000000000000000000)
  centralHi := (345816059669357012387/100000000000000000000)
  directionLo := (349399741495348174491/100000000000000000000)
  directionHi := (87349935373837043623/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree050.table
  base := (-6990209015662396918462160016471889535579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-8904547010515405521415130013754897000000000000)
      constant := (116094608328597446780719358929201818357110751833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree050.table
  base := (-349513101379804935627938294670848022521/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-20040463969167262174322560896177424500000000000)
      constant := (261351507863542485348011485406404424629429859015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349399741495348174491/100000000000000000000)
  centralHi := (87349935373837043623/25000000000000000000)
  directionLo := (35294703793741061563/10000000000000000000)
  directionHi := (352947037937410615631/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree051.table
  base := (-6909774708638662314020701789320486797747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-9082380762495259251304109298514892000000000000)
      constant := (120874830805626030822043589815230995518285540769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree051.table
  base := (-1381964036513743777700232598561007193233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-9084753144458704471820237624085329500000000000)
      constant := (120938938307349594193350853053598409078936798455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35294703793741061563/10000000000000000000)
  centralHi := (352947037937410615631/100000000000000000000)
  directionLo := (356459035262914618863/100000000000000000000)
  directionHi := (22278689703932163679/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree052.table
  base := (-6807261097334671230437510722510659781349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-9260214514475112981193088583274887000000000000)
      constant := (125755049866149607414681299209816930994237643623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree052.table
  base := (-3403650045431501598920595752595324952599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-41681850361793815897737016824413116500000000000)
      constant := (566197633946468940561075383964875102467953406357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356459035262914618863/100000000000000000000)
  centralHi := (22278689703932163679/6250000000000000000)
  directionLo := (359936766741525930337/100000000000000000000)
  directionHi := (179968383370762965169/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree053.table
  base := (-3341377241273137512405222103660727332483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1585309359102217944895163440010000000000000)
      linear := (-89038191192971384066811961019197000000000000)
      constant := (1233351343895524967584930011888296492266953197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree053.table
  base := (-1670696976852224599210178939266834752333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7133892115959980752028235480045000000000000)
      linear := (-400776524278523223323424191890964625000000000)
      constant := (5553020253160871007337870062586749759277654123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359936766741525930337/100000000000000000000)
  centralHi := (179968383370762965169/50000000000000000000)
  directionLo := (181690608098024350287/50000000000000000000)
  directionHi := (14535248647841948023/4000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree054.table
  base := (-653632742930605067154706557500551008673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-4807941009217410220485523576397438500000000000)
      constant := (67907694589268349791012022024178862926799042855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree054.table
  base := (-817044508879994899312438652745284097811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1202299244034808540189691996013094000000000000)
      constant := (16985907609921421794863643961029497828923041697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181690608098024350287/50000000000000000000)
  centralHi := (14535248647841948023/4000000000000000000)
  directionLo := (91698330313280284199/25000000000000000000)
  directionHi := (366793321253121136797/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree055.table
  base := (-796005119374383200639448887141947215603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1224214471301834271357503304694359000000000000)
      constant := (17624434217598251817384563853560864653753199681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree055.table
  base := (-3184032745017889777588115840211416752519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-44083233996982753221374859372500517750000000000)
      constant := (634815142084110486260828068910507608594375670917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91698330313280284199/25000000000000000000)
  centralHi := (366793321253121136797/100000000000000000000)
  directionLo := (370173976324202408393/100000000000000000000)
  directionHi := (185086988162101204197/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree056.table
  base := (-6177946368484732997313309679989660729327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-9971549522394527900749005722314867000000000000)
      constant := (146275482431328489363811384531589989373963517429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree056.table
  base := (-772245922376847744127864863892657386349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-11220923802178099748980201722132412875000000000)
      constant := (164646872410408904167608771806645024745552807607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370173976324202408393/100000000000000000000)
  centralHi := (185086988162101204197/50000000000000000000)
  directionLo := (186762017671853585969/50000000000000000000)
  directionHi := (373524035343707171939/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree057.table
  base := (-5966086816049055016311108897515005253769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10149383274374381630637985007074862000000000000)
      constant := (151655403722644660074951944611872734688834774963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree057.table
  base := (-1491526200720180154944510223021343961673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-2538008690024558042803708578031043625000000000)
      constant := (37933870269652149308989392081548511208009189571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186762017671853585969/50000000000000000000)
  centralHi := (373524035343707171939/100000000000000000000)
  directionLo := (75368862857607940409/20000000000000000000)
  directionHi := (188422157144019851023/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree058.table
  base := (-5732498580866350899845951410691169658479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10327217026354235360526964291834857000000000000)
      constant := (157135227920848925586794293544313261628835190133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree058.table
  base := (-573251397460870878069910738735000188879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-46484617632171690545012701920587919000000000000)
      constant := (707481624182338299269157218681475645097898391985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75368862857607940409/20000000000000000000)
  centralHi := (188422157144019851023/50000000000000000000)
  directionLo := (95033898374145515771/25000000000000000000)
  directionHi := (76027118699316412617/20000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree059.table
  base := (-5477212175439966174556130847767376769259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10505050778334089090415943576594852000000000000)
      constant := (162714946873824229564949898505371340583926765193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree059.table
  base := (-5477225346170406298053856967006209642813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-94570157687802672639117298873234105500000000000)
      constant := (1465206662031367285061524215081940470388031501159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95033898374145515771/25000000000000000000)
  centralHi := (76027118699316412617/20000000000000000000)
  directionLo := (191699309906670323061/50000000000000000000)
  directionHi := (383398619813340646123/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree060.table
  base := (-5200253259978936738086530272452982484081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10682884530313942820304922861354847000000000000)
      constant := (168394553725855543261537283152266551810780626987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree060.table
  base := (-5200264525612660358190921847350788689751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10685675567917996020912132656143597000000000000)
      constant := (168483278792393459107042504450732442733393156077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191699309906670323061/50000000000000000000)
  centralHi := (383398619813340646123/100000000000000000000)
  directionLo := (193317054282951431763/50000000000000000000)
  directionHi := (386634108565902863527/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree061.table
  base := (-4901643414498899825702192336220559386027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-10860718282293796550193902146114842000000000000)
      constant := (174174042711345348829498980244677013674657008329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree061.table
  base := (-4901653048026132894560054868329457100367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-97772002534721255737301088937350640500000000000)
      constant := (1568391737882845142457179274947344476826237827581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193317054282951431763/50000000000000000000)
  centralHi := (386634108565902863527/100000000000000000000)
  directionLo := (194921372698279421769/50000000000000000000)
  directionHi := (389842745396558843539/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree062.table
  base := (-2290700393984343129573523586791583722651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-5519276017136825140041440715437418500000000000)
      constant := (90026704490689598415848599368387234202068164377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree062.table
  base := (-45814090237082584045563774993870509669/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-24843231239545136821598245992352227000000000000)
      constant := (405333326184509212085040374664748520081420959175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194921372698279421769/50000000000000000000)
  centralHi := (389842745396558843539/100000000000000000000)
  directionLo := (19651259397943305911/5000000000000000000)
  directionHi := (393025187958866118221/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree063.table
  base := (-4239540644103126683936813419995178170203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-11216385786253504009971860715634832000000000000)
      constant := (186032648457904604820077567533568665200232353881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree063.table
  base := (-4239547683102393721040880613029058370661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-11219316375737759870609431000163019500000000000)
      constant := (186130463674960784759597276173569068466060388647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19651259397943305911/5000000000000000000)
  centralHi := (393025187958866118221/100000000000000000000)
  directionLo := (19809103374577424329/5000000000000000000)
  directionHi := (396182067491548486581/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree064.table
  base := (-3876075820273697409705943387283760456971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-11394219538233357739860840000394827000000000000)
      constant := (192111757711122523354566121107551803867429687017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree064.table
  base := (-1938040917484148595521890686268306088483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-51287384902549565192288387016762721500000000000)
      constant := (864957156046641423847080648882619646716795582969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19809103374577424329/5000000000000000000)
  centralHi := (396182067491548486581/100000000000000000000)
  directionLo := (49914248785049739213/12500000000000000000)
  directionHi := (79862798056079582741/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree065.table
  base := (-1745508556690057592268228575936502144561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-5786026645106605734874909642577411000000000000)
      constant := (99145366928196432206213770954422715506281203947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree065.table
  base := (-1745511125806259432895099529175190384851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-52087846114279210966834334532791855250000000000)
      constant := (892776847945659540920997608063364269897836333993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49914248785049739213/12500000000000000000)
  centralHi := (79862798056079582741/20000000000000000000)
  directionLo := (402421539017768728159/100000000000000000000)
  directionHi := (2515134618861054551/625000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree066.table
  base := (-3084373604317647847233579159475754934073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-11749887042193065199638798569914817000000000000)
      constant := (204569574467545596599364721706615108626998914371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree066.table
  base := (-3084377992800694399082266297446300625629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-11752957183557523720306729344182442000000000000)
      constant := (204676922520448098634341971780385108710448823183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402421539017768728159/100000000000000000000)
  centralHi := (2515134618861054551/625000000000000000)
  directionLo := (202752637034148953033/50000000000000000000)
  directionHi := (405505274068297906067/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree067.table
  base := (-332019116352427770253147209389362085529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1490965099271614866190972231834351500000000000)
      constant := (26368534687998080904799826031611234705710460483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree067.table
  base := (-2656156678119812508067580767011837797587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-107377537075477005031852459129700245500000000000)
      constant := (1899530114149693034466670611427586747419072596041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202752637034148953033/50000000000000000000)
  centralHi := (405505274068297906067/100000000000000000000)
  directionLo := (408565734648637951093/100000000000000000000)
  directionHi := (204282867324318975547/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree068.table
  base := (-2206361516893880988907271046831473668559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-12105554546152772659416757139434807000000000000)
      constant := (217426841249388408625295485337568568185550086293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree068.table
  base := (-2206364716000785148422632797983728812767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-108978459498936296580944354161758513000000000000)
      constant := (1957867114878862113755368217778404600497159420781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408565734648637951093/100000000000000000000)
  centralHi := (204282867324318975547/50000000000000000000)
  directionLo := (82320687985647223201/20000000000000000000)
  directionHi := (205801719964118058003/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree069.table
  base := (-1735004765767341116873040601401741044343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-12283388298132626389305736424194802000000000000)
      constant := (224005264260160696024589677726032387827459747661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree069.table
  base := (-108437968518917424803879178791267734033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1535824748922160946250503461025233062500000000)
      constant := (28015323498768288587015569857116006167406027582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82320687985647223201/20000000000000000000)
  centralHi := (205801719964118058003/50000000000000000000)
  directionLo := (414618890057523689199/100000000000000000000)
  directionHi := (1036547225143809223/250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree070.table
  base := (-248417444428102512436282587481898537537/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-12461222050112480119194715708954797000000000000)
      constant := (230683545322080186639107239222157908610153135495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree070.table
  base := (-1242089552259961689510518851185695537701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-112180304345854879679128144225875048000000000000)
      constant := (2077238634346636354757477901112905485932452296543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414618890057523689199/100000000000000000000)
  centralHi := (1036547225143809223/250000000000000000)
  directionLo := (417612567129281629931/100000000000000000000)
  directionHi := (104403141782320407483/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree071.table
  base := (-363806354321213381427487625460540632829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265000000000000000000000000000000000000000
      center := (4664)
      previous := (2332)
      next := (2332)
      square := (16667604846740240245872577330000000000000)
      linear := (-1253625848253554240139227831156000000000000)
      constant := (23553033466955327737795810467864560096460063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree071.table
  base := (-727614696669666823344588578870647628861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4770000000000000000000000000000000000000000
      center := (83952)
      previous := (41976)
      next := (41976)
      square := (300016887241324324425706391940000000000000)
      linear := (-22571161826882398577310065315995500000000000)
      constant := (424176380285009531434304259089939904206033303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417612567129281629931/100000000000000000000)
  centralHi := (104403141782320407483/25000000000000000000)
  directionLo := (420584936078415194429/100000000000000000000)
  directionHi := (42058493607841519443/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree072.table
  base := (-11974027536713093617630146441209808831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1602111194259023447371584284809348375000000000)
      constant := (30542459709550725562911298469163718928490390474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree072.table
  base := (-191586136418402063930771096358356074133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-12820238799197051419701326032221287000000000000)
      constant := (244467420023385024080474184660722060432605663991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420584936078415194429/100000000000000000000)
  centralHi := (42058493607841519443/10000000000000000000)
  directionLo := (105884111381223184689/25000000000000000000)
  directionHi := (423536445524892738757/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree073.table
  base := (45749359689131787168540397987523524779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1624340413256505163607706695404347750000000000)
      constant := (31414690923399288803370456138647241021123279767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree073.table
  base := (365993431203909576598756568716214160037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-116983071616232754326403829322049850500000000000)
      constant := (2263039569442045495641014065538201097850141088609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105884111381223184689/25000000000000000000)
  centralHi := (423536445524892738757/100000000000000000000)
  directionLo := (213233764282088000779/50000000000000000000)
  directionHi := (426467528564176001559/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree074.table
  base := (945122970781286843010500342543829446649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-13172557058031895038750632847994777000000000000)
      constant := (258395231938423238218007762507784738044749553277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree074.table
  base := (945121737505597619313702036175667093691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-118583994039692045875495724354108118000000000000)
      constant := (2326771495256275447618761793792692500227304349887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213233764282088000779/50000000000000000000)
  centralHi := (426467528564176001559/100000000000000000000)
  directionLo := (429378603509085106773/100000000000000000000)
  directionHi := (214689301754542553387/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree075.table
  base := (77289896285346282454305527149976440519/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-3337597702502937192159903033188693000000000000)
      constant := (66393197704713570949719264593264574762088913935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree075.table
  base := (96612304642098597843099903465558316777/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1669234950877101908674828047030088687500000000)
      constant := (33213924348121499206034881095460612937227147842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429378603509085106773/100000000000000000000)
  centralHi := (214689301754542553387/50000000000000000000)
  directionLo := (216135037293348132741/50000000000000000000)
  directionHi := (432270074586696265483/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree076.table
  base := (2168018132731064926420545579819162969969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-13528224561991602498528591417514767000000000000)
      constant := (272850203598456765633165732566924419728175527637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree076.table
  base := (135501077280237020633242154195197814233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56711250000000000000000000000000000000000000
      center := (998118)
      previous := (499059)
      next := (499059)
      square := (3566946057979990376014117740022500000000000)
      linear := (-287230752091062804183206401929775125000000000)
      constant := (5794652686339837617113537050130519609267873954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216135037293348132741/50000000000000000000)
  centralHi := (432270074586696265483/100000000000000000000)
  directionLo := (13598197893548728541/3125000000000000000)
  directionHi := (435142332593559313313/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree077.table
  base := (140589111897781864962196300375491719429/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-3426514578492864057104392675568690500000000000)
      constant := (70056867478876418841471804772073106542650021085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree077.table
  base := (2811781474119186302937639015302532033319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-123386761310069920522771409450282920500000000000)
      constant := (2523362049840112106896503516130529337221566434683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13598197893548728541/3125000000000000000)
  centralHi := (435142332593559313313/100000000000000000000)
  directionLo := (87599151102448391539/20000000000000000000)
  directionHi := (6843683679878780589/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree078.table
  base := (3477089102527158923945603966749898753043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-13883892065951309958306549987034757000000000000)
      constant := (287704589465730111158092530316643776699546757439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree078.table
  base := (173854422582338762332046091124611674041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-3471880103709144779773980680065033000000000000)
      constant := (71963624523065473016027647494616364858317780465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87599151102448391539/20000000000000000000)
  centralHi := (6843683679878780589/1562500000000000000)
  directionLo := (440830709091954562117/100000000000000000000)
  directionHi := (220415354545977281059/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree079.table
  base := (832787553694953551167096702270765615827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3170618718204435889790326880020000000000000)
      linear := (-265315581470399314871613759845184000000000000)
      constant := (5571350226286530639334258099014117834846919535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree079.table
  base := (208196860696792662571979939468481844279/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-31647151539247125905238799878599863875000000000)
      constant := (664729508920539922471814756041106194040951147015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440830709091954562117/100000000000000000000)
  centralHi := (220415354545977281059/50000000000000000000)
  directionLo := (221823773697890252759/50000000000000000000)
  directionHi := (443647547395780505519/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree080.table
  base := (4872327429976548438530032134202966121059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-14239559569911017418084508556554747000000000000)
      constant := (302958387282579854954245608351081419067461696207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree080.table
  base := (1218081739398288985117788743932951853393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-32047382145111948792511773636614430750000000000)
      constant := (682011176615928798304264815217041678159739111901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221823773697890252759/50000000000000000000)
  centralHi := (443647547395780505519/100000000000000000000)
  directionLo := (446446613316830021813/100000000000000000000)
  directionHi := (223223306658415010907/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree081.table
  base := (700282176148914105217880519945449917603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1802174165236358893496685980164342750000000000)
      constant := (38841883144101305076293670149705061839273246319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree081.table
  base := (224090280274149058134003586833825550251/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-14421161222656342968793221064279554500000000000)
      constant := (310896721505567575688117560164990742046555260575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446446613316830021813/100000000000000000000)
  centralHi := (223223306658415010907/50000000000000000000)
  directionLo := (449228239065447652917/100000000000000000000)
  directionHi := (224614119532723826459/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree082.table
  base := (63537271359302132969554778868483906923/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-3648806768467681219465616781518684250000000000)
      constant := (79652898862884703963721424964788612896608466975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree082.table
  base := (3176863396651611678310775217448716042351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-65695686713683189134115442305287129000000000000)
      constant := (1434497697787276985110525733198276782644397393507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449228239065447652917/100000000000000000000)
  centralHi := (224614119532723826459/50000000000000000000)
  directionLo := (451992746629433012747/100000000000000000000)
  directionHi := (112998186657358253187/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree083.table
  base := (3563368065278970964788792985834662981421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-7386530412925289303875723205417366000000000000)
      constant := (163293989025309688288538428884190555381485192833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree083.table
  base := (1781683959705649806861996376354313831573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-33248073962706417454330694910658131375000000000)
      constant := (735204852846847014496780885162441990198436928161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451992746629433012747/100000000000000000000)
  centralHi := (112998186657358253187/25000000000000000000)
  directionLo := (90948089641815933521/20000000000000000000)
  directionHi := (227370224104539833803/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree084.table
  base := (316851359584411622965721898212288271003/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-14950894577830432337640425695594727000000000000)
      constant := (334664212842257379888730701555816587855717112975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree084.table
  base := (99016046765536724658436396188216726273/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1869350253809513352311314926037372125000000000)
      constant := (41854757500299616140514819439097784336585362290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90948089641815933521/20000000000000000000)
  centralHi := (227370224104539833803/50000000000000000000)
  directionLo := (457471646628696002773/100000000000000000000)
  directionHi := (228735823314348001387/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree085.table
  base := (546085648356027115992672833048945737277/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-1891091041226285758441175622544340250000000000)
      constant := (42855037466972095100249255908285120357368515842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree085.table
  base := (136521408785620109733024465323689247807/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-17024267587218031614438321213343632562500000000)
      constant := (385895597582960299217286263370364957654753076992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457471646628696002773/100000000000000000000)
  centralHi := (228735823314348001387/50000000000000000000)
  directionLo := (57523329465767944711/12500000000000000000)
  directionHi := (460186635726143557689/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree086.table
  base := (4787497498661454852777651370932006616359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-7653281040895069898709192132557358500000000000)
      constant := (175558119327450687287720726246093455503712483107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree086.table
  base := (2393748704346002781703409922020049183511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-34448765780300886116149616184701832000000000000)
      constant := (790421533157376064801327929990289692513930659627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57523329465767944711/12500000000000000000)
  centralHi := (460186635726143557689/100000000000000000000)
  directionLo := (28930356295113201343/6250000000000000000)
  directionHi := (462885700721811221489/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree087.table
  base := (5217078810166986018799049104063654535579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-7742197916884996763653681774937356000000000000)
      constant := (179746014767734045030077455496761231241984248167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree087.table
  base := (10434157467206590276845378153416543321633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-15488442838295870668187817752318399500000000000)
      constant := (359678510593723208405420679209117960956995653509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28930356295113201343/6250000000000000000)
  centralHi := (462885700721811221489/100000000000000000000)
  directionLo := (465569118568336773379/100000000000000000000)
  directionHi := (23278455928416838669/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree088.table
  base := (11314858040711515803197428069890336666699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-15662229585749847257196342834634707000000000000)
      constant := (367967672323503124075927713779493561918251971927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree088.table
  base := (11314857910417619393916073620250669502009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-140996907968122127562782254802923863000000000000)
      constant := (3313426168321587250957145362121754685605742255013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465569118568336773379/100000000000000000000)
  centralHi := (23278455928416838669/5000000000000000000)
  directionLo := (93647431656457907219/20000000000000000000)
  directionHi := (14632411196321548003/3125000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree089.table
  base := (12217096088518584870639818971145441582199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-15840063337729700987085322119394702000000000000)
      constant := (376543166973603910242181577033155576251340853427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree089.table
  base := (12217095977667499630134788490252269518001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-142597830391581419111874149834982130500000000000)
      constant := (3390644851156528621773501378441609556013520930557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93647431656457907219/20000000000000000000)
  centralHi := (14632411196321548003/3125000000000000000)
  directionLo := (235445040629469250069/50000000000000000000)
  directionHi := (470890081258938500139/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree090.table
  base := (13140871620804795507460449366205466414673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16017897089709554716974301404154697000000000000)
      constant := (385218513447577965685962676987682630578407429429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree090.table
  base := (13140871526506966186514216415523175676643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16022083646115634517885116096337822000000000000)
      constant := (385418071500645067920066182383515920602555740239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235445040629469250069/50000000000000000000)
  centralHi := (470890081258938500139/100000000000000000000)
  directionLo := (47352814157114838051/10000000000000000000)
  directionHi := (473528141571148380511/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree091.table
  base := (14086184517320874588084370864849556029461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16195730841689408446863280688914692000000000000)
      constant := (393993711713297931358491777956814248370559183753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree091.table
  base := (14086184437114205891304430603224923232761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-145799675238500002210057939899098665500000000000)
      constant := (3547779545081299839863604662432648593561923091877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47352814157114838051/10000000000000000000)
  centralHi := (473528141571148380511/100000000000000000000)
  directionLo := (238075793126685489159/50000000000000000000)
  directionHi := (476151586253370978319/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree092.table
  base := (15053034676913789726774057290425638256413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16373564593669262176752259973674687000000000000)
      constant := (402868761743738448138174227859355765549880630449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree092.table
  base := (15053034608700745892173407218729939150853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-147400597661959293759149834931156933000000000000)
      constant := (3627695555640659679606143507148904907294757637121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238075793126685489159/50000000000000000000)
  centralHi := (476151586253370978319/100000000000000000000)
  directionLo := (2992254097322689393/625000000000000000)
  directionHi := (478760655571630302881/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree093.table
  base := (4010355503623591989328175175116145237597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-4137849586412278976660309814608670500000000000)
      constant := (102960915879041496604026745866723469168439503281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree093.table
  base := (3208284391297654242257002782359141982881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16555724453935398367582414440357244500000000000)
      constant := (412056741664447871086672384300523348783086327065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2992254097322689393/625000000000000000)
  centralHi := (478760655571630302881/100000000000000000000)
  directionLo := (481355583280336596891/100000000000000000000)
  directionHi := (120338895820084149223/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree094.table
  base := (17051346458486473876748191204318269724719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16729232097628969636530218543194677000000000000)
      constant := (420918417011457335368277120723614453077162349387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree094.table
  base := (3410269281833133235957999891903698120979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-150602442508877876857333624995273468000000000000)
      constant := (3790224902927941678025987368127272528650934506515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481355583280336596891/100000000000000000000)
  centralHi := (120338895820084149223/25000000000000000000)
  directionLo := (241968298433353093511/50000000000000000000)
  directionHi := (483936596866706187023/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree095.table
  base := (18082807948681263264973271610507573039911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-16907065849608823366419197827954672000000000000)
      constant := (430093022213526317457865923403898440749292141603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree095.table
  base := (4520701976687497002859277687226991861761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-38050841233084292101606380006832933875000000000)
      constant := (968209559835039947346667820246244856545921694877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241968298433353093511/50000000000000000000)
  centralHi := (483936596866706187023/100000000000000000000)
  directionLo := (778406268453616793/160000000000000000)
  directionHi := (243251958891755247813/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree096.table
  base := (19135806434432177943509450194348621938193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-17084899601588677096308177112714667000000000000)
      constant := (439367479108841539796654757438186876369092838389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree096.table
  base := (298996974981050049088492864966729238577/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2136170657719395277159964098047083375000000000)
      constant := (54949315056880077420502760471736875356866662568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (778406268453616793/160000000000000000)
  centralHi := (243251958891755247813/50000000000000000000)
  directionLo := (244528880835414091197/50000000000000000000)
  directionHi := (97811552334165636479/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree097.table
  base := (20210341873136566901136578983654830765431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-17262733353568530826197156397474662000000000000)
      constant := (448741787686020724306022902232306753287592496563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree097.table
  base := (1010517092141935634429886558194705788191/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-38851302444813937876152327522862067625000000000)
      constant := (1010190559272878250670743334911662267661707181935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244528880835414091197/50000000000000000000)
  centralHi := (97811552334165636479/20000000000000000000)
  directionLo := (245799169283714432681/50000000000000000000)
  directionHi := (491598338567428865363/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree098.table
  base := (10653207114479207162509175615408564386443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-8720283552774192278043067841117328500000000000)
      constant := (229107973967744727566603721601789556622819135639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree098.table
  base := (665825443850258399603281020919924374789/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-19625766525339380381712650640438317250000000000)
      constant := (515759112280346051491203911886509942215415553892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245799169283714432681/50000000000000000000)
  centralHi := (491598338567428865363/100000000000000000000)
  directionLo := (247062926556187430941/50000000000000000000)
  directionHi := (494125853112374861883/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree099.table
  base := (560600586793847129467345528216464135733/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2202300107191029785746889370874331500000000000)
      constant := (58473744981149264180001500009732883604868464045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree099.table
  base := (22424023449871096192761098534256193144309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-17623006069574926066977011128396089500000000000)
      constant := (468031407497437279836369210496850582344069468457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247062926556187430941/50000000000000000000)
  centralHi := (494125853112374861883/100000000000000000000)
  directionLo := (15520015773043393401/3125000000000000000)
  directionHi := (496640504737388588833/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree100.table
  base := (23563169576167480380825926782191390694267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-17796234609508092015864094251754647000000000000)
      constant := (477463823420360394470378506017489057925959397191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree100.table
  base := (23563169557573100060625333456983025693883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-160207977049633626151884995187623073000000000000)
      constant := (4299391544733289411939424760422467220813406224831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15520015773043393401/3125000000000000000)
  centralHi := (496640504737388588833/100000000000000000000)
  directionLo := (499142487850497392131/100000000000000000000)
  directionHi := (124785621962624348033/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree101.table
  base := (24723852520871708978453211371994388671331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-17974068361487945745753073536514642000000000000)
      constant := (487237538643290168483931389719641855991985517263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree101.table
  base := (12361926252536571685933921964922407395301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-80904449736546458850488445109840670250000000000)
      constant := (2193699764980377283729434762741712361635785286657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499142487850497392131/100000000000000000000)
  centralHi := (124785621962624348033/25000000000000000000)
  directionLo := (501631992011434390413/100000000000000000000)
  directionHi := (250815996005717195207/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree102.table
  base := (25906072287927487480094265624234906439823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-18151902113467799475642052821274637000000000000)
      constant := (497111105513190596727001088624403771658246830379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree102.table
  base := (25906072274505669275646276802667405968411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-18156646877394689916674309472415512000000000000)
      constant := (497367402568485803922340694832311603792298272103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501631992011434390413/100000000000000000000)
  centralHi := (250815996005717195207/50000000000000000000)
  directionLo := (252054601049621595401/50000000000000000000)
  directionHi := (504109202099243190803/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree103.table
  base := (27109828862246095822770995240334556590619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-18329735865447653205531032106034632000000000000)
      constant := (507084524026030380594201556343740721425485450087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree103.table
  base := (27109828850844553534246634037755195757129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-165010744320011500799160680283797875500000000000)
      constant := (4566112824164011243247350086465079126197299836853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252054601049621595401/50000000000000000000)
  centralHi := (504109202099243190803/100000000000000000000)
  directionLo := (253287149236252930953/50000000000000000000)
  directionHi := (506574298472505861907/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree104.table
  base := (7083780557784140969747754982290523126517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-4626892404356876733855002847698656750000000000)
      constant := (129289448544604708880915067789532574185280926441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree104.table
  base := (28335122221452108630226670857760311240229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-166611666743470792348252575315856143000000000000)
      constant := (4656818133073283551313842652631163530214871323553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253287149236252930953/50000000000000000000)
  centralHi := (506574298472505861907/100000000000000000000)
  directionLo := (50902745712258714481/10000000000000000000)
  directionHi := (509027457122587144811/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree105.table
  base := (7395488095981230823601444389454534356661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-4671350842351840166327247668888655500000000000)
      constant := (131832728991876041342060216169209843104547189353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree105.table
  base := (739548809392492876969958169881731025159/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2336285960651806720796450977054366812500000000)
      constant := (65950313191925444973861950384384933547564652535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50902745712258714481/10000000000000000000)
  centralHi := (509027457122587144811/100000000000000000000)
  directionLo := (255734424910131689113/50000000000000000000)
  directionHi := (511468849820263378227/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree106.table
  base := (15425159655816956800245043886139537895113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (443608)
      previous := (221804)
      next := (221804)
      square := (1585309359102217944895163440010000000000000)
      linear := (-177955067182898249011301603399194500000000000)
      constant := (5071734805574414042611189234803230160529264633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree106.table
  base := (7712579826162175932708863070576020327157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1996236)
      previous := (998118)
      next := (998118)
      square := (7133892115959980752028235480045000000000000)
      linear := (-801007130143346110596397949905531500000000000)
      constant := (22834556954615863982013151343264178950597785933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255734424910131689113/50000000000000000000)
  centralHi := (511468849820263378227/100000000000000000000)
  directionLo := (102779728851216371151/20000000000000000000)
  directionHi := (128474661064020463939/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree107.table
  base := (8035055751678385894836502675209723776713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-4760267718341767031271737311268653000000000000)
      constant := (136994178611638212791409101876424015014970742349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree107.table
  base := (32140223000781919823293934724670011286181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-171414434013848666995528260412030945500000000000)
      constant := (4934328706735001502414464561672876380656390526817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102779728851216371151/20000000000000000000)
  centralHi := (128474661064020463939/25000000000000000000)
  directionLo := (516317004174775181579/100000000000000000000)
  directionHi := (25815850208738759079/5000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree108.table
  base := (3345166346281443311390660666845417044299/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-9609452312673460927487964264917303500000000000)
      constant := (279224695566401335190387392526349992289882483635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree108.table
  base := (33451663457777919457671479417621703932109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-19223928493034217616068906160454357000000000000)
      constant := (558736716319194086736093208458885359504653357857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516317004174775181579/100000000000000000000)
  centralHi := (25815850208738759079/5000000000000000000)
  directionLo := (518724089504035518579/100000000000000000000)
  directionHi := (25936204475201775929/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree109.table
  base := (34784640674597142946457749829543651311161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-19396738377326775584864907814594602000000000000)
      constant := (569021919448210792157399935385612691139256817853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree109.table
  base := (1087020020947532114673089475318275879541/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-21827034857595906261714006309518435062500000000)
      constant := (640478911847377144421558498576380514689216498348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518724089504035518579/100000000000000000000)
  centralHi := (25936204475201775929/5000000000000000000)
  directionLo := (260560028238967656807/50000000000000000000)
  directionHi := (104224011295587062723/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree110.table
  base := (7227830927514355667908087454568160534553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-19574572129306629314753887099354597000000000000)
      constant := (579694299391577637848820724319622365772490643345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree110.table
  base := (36139154633941562651874865583402096305771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-176217201284226541642803945508205748000000000000)
      constant := (5219931250443065021980506374168701647924215798447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260560028238967656807/50000000000000000000)
  centralHi := (104224011295587062723/20000000000000000000)
  directionLo := (16359533054852001017/3125000000000000000)
  directionHi := (104701011551052806509/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree111.table
  base := (37515205347963059925997067841103390514443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-19752405881286483044642866384114592000000000000)
      constant := (590466530961894554740675554080745129091415279639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree111.table
  base := (18757602672440717637645074232737716092271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-9878784650426990732883102252236889750000000000)
      constant := (295385017436436324495903166345390681110582819883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16359533054852001017/3125000000000000000)
  centralHi := (104701011551052806509/20000000000000000000)
  directionLo := (262939621266517272737/50000000000000000000)
  directionHi := (21035169701321381819/4000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree112.table
  base := (19456396401298409125921894411494730176369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-9965119816633168387265922834437293500000000000)
      constant := (300669307079156745228717598394266808545411034837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree112.table
  base := (38912792799981093946044911159703527866239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-179419046131145124740987735572322283000000000000)
      constant := (5414828485009786290308131654812177946855460051123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262939621266517272737/50000000000000000000)
  centralHi := (21035169701321381819/4000000000000000000)
  directionLo := (528242756655397982107/100000000000000000000)
  directionHi := (132060689163849495527/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree113.table
  base := (20165958499402255269177078879459414681117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-10054036692623095252210412476817291000000000000)
      constant := (306155274490060741209639486315867206792348072241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree113.table
  base := (2016595849829221244155471823268406977839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-45254992138651104072519907651095137625000000000)
      constant := (1378406440974618898285289720562782812594089311615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528242756655397982107/100000000000000000000)
  centralHi := (132060689163849495527/25000000000000000000)
  directionLo := (132648935679548011707/25000000000000000000)
  directionHi := (530595742718192046829/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree114.table
  base := (41772577934342898265253510240041487313111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-20285907137226044234309804238394577000000000000)
      constant := (623382335426719197861029538696241834789905805203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree114.table
  base := (2088628896622937813846798199090260192723/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-5072802527168436328865875712123300500000000000)
      constant := (155925615292126476744360776178559794229226910395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132648935679548011707/25000000000000000000)
  centralHi := (530595742718192046829/100000000000000000000)
  directionLo := (66617292521166858607/12500000000000000000)
  directionHi := (532938340169334868857/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree115.table
  base := (43234775607326478495172620919462073447553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-20463740889205897964198783523154572000000000000)
      constant := (634553973497602881306401146938449806486703077669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree115.table
  base := (21617387802863783831729284303908547191437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-92110906700761499694131710334248542750000000000)
      constant := (2856958822429753399429052933339840755798062678409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66617292521166858607/12500000000000000000)
  centralHi := (532938340169334868857/100000000000000000000)
  directionLo := (535270685405264396327/100000000000000000000)
  directionHi := (66908835675658049541/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree116.table
  base := (44718510016170644038986720722303127156181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-20641574641185751694087762807914567000000000000)
      constant := (645825463192349168498853765430316092891698346313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree116.table
  base := (22359255007406943394986368862813920810181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-92911367912491145468677657850277676500000000000)
      constant := (2907706123461772290827733125129528238231566394817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535270685405264396327/100000000000000000000)
  centralHi := (66908835675658049541/12500000000000000000)
  directionLo := (268796455931806031033/50000000000000000000)
  directionHi := (537592911863612062067/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree117.table
  base := (23111890579771934528964098786603151513433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-10409704196582802711988371046337281000000000000)
      constant := (328598402255301155842733167475415489393048434909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree117.table
  base := (23111890579196338344993600852844139972901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-10412425458246754582580400596256312250000000000)
      constant := (328766997594748910237557430296647646323042378873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268796455931806031033/50000000000000000000)
  centralHi := (537592911863612062067/100000000000000000000)
  directionLo := (107981030022457779101/20000000000000000000)
  directionHi := (269952575056144447753/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree118.table
  base := (9550117807265497429522661638382496128103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-20997242145145459153865721377434557000000000000)
      constant := (668667997452063433406980437656577794190168314095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree118.table
  base := (23875294517675392615966023454653536001623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-94512290335950437017769552882335944000000000000)
      constant := (3010549387101318784484888497546087128786204596011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107981030022457779101/20000000000000000000)
  centralHi := (269952575056144447753/50000000000000000000)
  directionLo := (542207527935152377041/100000000000000000000)
  directionHi := (271103763967576188521/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree119.table
  base := (49298933645581856457211864396363325487651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-21175075897125312883754700662194552000000000000)
      constant := (680239042016481486731184219680391467698012180623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree119.table
  base := (9859786728950651229038578900161803009747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-190625503095360165584631000796730155500000000000)
      constant := (6125290699412767980091496300586631689251666085395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542207527935152377041/100000000000000000000)
  centralHi := (271103763967576188521/50000000000000000000)
  directionLo := (272250085207206539769/50000000000000000000)
  directionHi := (544500170414413079539/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree120.table
  base := (50868814986517897782481530830805514219683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-21352909649105166613643679946954547000000000000)
      constant := (691909938203645650999842643558269316650615366159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree120.table
  base := (12717203746453747813927106090410399373529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-5339622931078318253714524884133011750000000000)
      constant := (173066159231499550120307369336186768256823863517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272250085207206539769/50000000000000000000)
  centralHi := (544500170414413079539/100000000000000000000)
  directionLo := (546783200009931471977/100000000000000000000)
  directionHi := (273391600004965735989/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree121.table
  base := (26230116529236576285016794455940610111371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-10765371700542510171766329615857271000000000000)
      constant := (351840343006689467586935592590069940219035324183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree121.table
  base := (52460233057876914101650743077597866660631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-193827347942278748682814790860846690500000000000)
      constant := (6336371872964700254768660487736064934042011895467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546783200009931471977/100000000000000000000)
  centralHi := (273391600004965735989/50000000000000000000)
  directionLo := (34316046039721695709/6250000000000000000)
  directionHi := (109811347327109426269/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree122.table
  base := (675914848261145540086299790915170107493/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2713572144133109259177704814559317125000000000)
      constant := (89443910680691599630810174872700270118792272890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree122.table
  base := (54073187860385920058368725906516627352977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-195428270365738040231906685892904958000000000000)
      constant := (6443261121303587359807344640930018622605492316189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34316046039721695709/6250000000000000000)
  centralHi := (109811347327109426269/20000000000000000000)
  directionLo := (275660448866287491391/50000000000000000000)
  directionHi := (551320897732574982783/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree123.table
  base := (27853839696653465951500972518361283109391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-10943205452522363901655308900617266000000000000)
      constant := (363760868249991308516990681984596430060935321643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree123.table
  base := (1392691984821950290688223637376806914019/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2736516566516629608069424735068933687500000000)
      constant := (90986798296521241819646078119557696818586616435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275660448866287491391/50000000000000000000)
  centralHi := (551320897732574982783/100000000000000000000)
  directionLo := (138393949585149007463/25000000000000000000)
  directionHi := (553575798340596029853/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree124.table
  base := (28681853827663935159264947855529965078533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-11032122328512290766599798542997263500000000000)
      constant := (369796019588311945430491170852321507609926897209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree124.table
  base := (57363707654964113042194424832254021624867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-198630115212656623330090475957021493000000000000)
      constant := (6659736941101590853531260762139806500476225318919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138393949585149007463/25000000000000000000)
  centralHi := (553575798340596029853/100000000000000000000)
  directionLo := (555821551165663314211/100000000000000000000)
  directionHi := (138955387791415828553/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree125.table
  base := (5904127264662661271609893116729543023989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-11121039204502217631544288185377261000000000000)
      constant := (375881096737684513499144463252556969585491065485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree125.table
  base := (59041272646318138670740786561303520786153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-200231037636115914879182370989079760500000000000)
      constant := (6769323512558987595869452235581140843234114699221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555821551165663314211/100000000000000000000)
  centralHi := (138955387791415828553/25000000000000000000)
  directionLo := (558058266646037527267/100000000000000000000)
  directionHi := (139514566661509381817/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree126.table
  base := (7592546795866066655505134900649393927029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2802489020123036124122194456939314625000000000)
      constant := (95504024924518081604154178904244067023666119017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree126.table
  base := (59316771842448200465382775705312926143/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2803221667494100089281587028071361500000000000)
      constant := (95552905440570317755585669742287332755487178592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558058266646037527267/100000000000000000000)
  centralHi := (139514566661509381817/25000000000000000000)
  directionLo := (560286053015560757907/100000000000000000000)
  directionHi := (140071513253890189477/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree127.table
  base := (62461012816003745015752226886394946361411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-22597745912964142722866534940274512000000000000)
      constant := (776402056938889348796661175225077241941717261103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree127.table
  base := (6246101281578195103335771340274116399193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-101716441241517248988683080526598147750000000000)
      constant := (3495596989293633488267462916671529568384034112505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560286053015560757907/100000000000000000000)
  centralHi := (140071513253890189477/25000000000000000000)
  directionLo := (281252508182385637381/50000000000000000000)
  directionHi := (562505016364771274763/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree128.table
  base := (64203187993659966649489396000408193341743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-22775579664943996452755514225034507000000000000)
      constant := (788871766103551742494967741761057714239693502539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree128.table
  base := (32101593996735958006046736795839247752857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-102516902453246894763229028042627281500000000000)
      constant := (3551738936578570064760832682570662486058866569349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281252508182385637381/50000000000000000000)
  centralHi := (562505016364771274763/100000000000000000000)
  directionLo := (35294703793741061563/6250000000000000000)
  directionHi := (564715260699856985009/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree129.table
  base := (65966899899736522312130239028971864580241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-22953413416923850182644493509794502000000000000)
      constant := (801441326890088905683790333888397065162996728693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree129.table
  base := (2638675995983083643113430867249037909637/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3170618718204435889790326880020000000000000)
      linear := (-433196493354199331395282916388496500000000000)
      constant := (15129268082663098915318823143988276393187002925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35294703793741061563/6250000000000000000)
  centralHi := (564715260699856985009/100000000000000000000)
  directionLo := (113383377599908052547/20000000000000000000)
  directionHi := (35432305499971266421/6250000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree130.table
  base := (8469018566762411909857585973423782287147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2891405896112962989066684099319312125000000000)
      constant := (101763842412308125749426275320998198747503925431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree130.table
  base := (67752148533964135970575981549900046979901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-208235649753412372624641846149371098000000000000)
      constant := (7330742985406420511535580094965511801953349808857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113383377599908052547/20000000000000000000)
  centralHi := (35432305499971266421/6250000000000000000)
  directionLo := (3556937489187388613/625000000000000000)
  directionHi := (569109998269982178081/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree131.table
  base := (69558933896636483596370665825490123136141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-23309080920883557642422452079314492000000000000)
      constant := (826880003328650172966555634744401150606152199393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree131.table
  base := (69558933896521907805710906074242132848127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-209836572176871664173733741181429365500000000000)
      constant := (7445724203085239866905996921125044473313018714739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3556937489187388613/625000000000000000)
  centralHi := (569109998269982178081/100000000000000000000)
  directionLo := (22851787583911590599/4000000000000000000)
  directionHi := (35705918099861860311/6250000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree132.table
  base := (71387255987255030476094492032142281265439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3170618718204435889790326880020000000000000)
      linear := (-443149333450253044760593044605179000000000000)
      constant := (15844322999634331025204814560342264739859077999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree132.table
  base := (892340699839473864655309756792479686579/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2936631869449041051705911614076217125000000000)
      constant := (105022285117590747686412086047432906940523711670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22851787583911590599/4000000000000000000)
  centralHi := (35705918099861860311/6250000000000000000)
  directionLo := (573471058201205823033/100000000000000000000)
  directionHi := (286735529100602911517/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree133.table
  base := (4577319675367351391661380196331188358721/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2958093553105408137775051331104310250000000000)
      constant := (106589760781794057997888742541595308073166631466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree133.table
  base := (36618557402897650574189013897025864177181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-106519208511895123635958765622772950250000000000)
      constant := (3839191980775058823757007915595396068864852313817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573471058201205823033/100000000000000000000)
  centralHi := (286735529100602911517/50000000000000000000)
  directionLo := (575639198479556841783/100000000000000000000)
  directionHi := (71954899809944605223/12500000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree134.table
  base := (4694281897027510241632907122943432760639/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-2980322772102889854011173741699309625000000000)
      constant := (108223363143728975928463949540698154396916407094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree134.table
  base := (75108510352370391491079924579683894516721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-214639339447249538821009426277604168000000000000)
      constant := (7796062502335838157555507062434434686784943097597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575639198479556841783/100000000000000000000)
  centralHi := (71954899809944605223/12500000000000000000)
  directionLo := (577799203061030947971/100000000000000000000)
  directionHi := (144449800765257736993/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree135.table
  base := (77001442626889655748003913823609164035303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24020415928802972561978369218354472000000000000)
      constant := (878955575667043414627106742973838812120304008419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree135.table
  base := (3850072131341526125894856297859112373353/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-6006673940853023065836147814157289875000000000)
      constant := (219851115300654687365187891698047802232660455345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577799203061030947971/100000000000000000000)
  centralHi := (144449800765257736993/25000000000000000000)
  directionLo := (579951162848854295289/100000000000000000000)
  directionHi := (57995116284885429529/10000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree136.table
  base := (78915911629182408809881378430117952926303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24198249680782826291867348503114467000000000000)
      constant := (892224097805975613032757791242129380837179151419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree136.table
  base := (39457955814566147587536549341195814811229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-108920592147084060959596608170860351500000000000)
      constant := (4017058453506602527394641649484342362625044370553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579951162848854295289/100000000000000000000)
  centralHi := (57995116284885429529/10000000000000000000)
  directionLo := (232838066826372411/40000000000000000)
  directionHi := (582095167065931027501/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree137.table
  base := (10106489669910317923352687979113531798589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-3047010429095335002719540973484307750000000000)
      constant := (113199058945827352070868052512991446029661918897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree137.table
  base := (2526622417476252371274786611358343892659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-27430263339703426683535638921722371312500000000)
      constant := (1019311596363082675438059639454284612021767413252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232838066826372411/40000000000000000)
  centralHi := (582095167065931027501/100000000000000000000)
  directionLo := (7302891291225110483/1250000000000000000)
  directionHi := (584231303298008838641/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree138.table
  base := (16561891963432145457459215856908730184047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24553917184742533751645307072634457000000000000)
      constant := (919060696948965188460059462909220544347311945655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree138.table
  base := (82809459817124741210542166652748902911269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24560336571231856113041889600648582000000000000)
      constant := (919529749166429751373118178709578575825012472537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7302891291225110483/1250000000000000000)
  centralHi := (584231303298008838641/100000000000000000000)
  directionLo := (293179828767714608211/50000000000000000000)
  directionHi := (586359657535429216423/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree139.table
  base := (84788539002793114878980107199604533739571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24731750936722387481534286357394452000000000000)
      constant := (932628773953008357802977753078106996030302402783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree139.table
  base := (42394269501381311314536972068423763338071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-111321975782272998283234450718947752750000000000)
      constant := (4198970910896383609503968462506605225764964489547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293179828767714608211/50000000000000000000)
  centralHi := (586359657535429216423/100000000000000000000)
  directionLo := (588480314213518676843/100000000000000000000)
  directionHi := (147120078553379669211/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree140.table
  base := (86789154916160455280568714460551083215499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-24909584688702241211423265642154447000000000000)
      constant := (946296702578743181279988423745158457055934514327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree140.table
  base := (867891549161346194761678106164734860163/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-56061218497001322028890199117488443250000000000)
      constant := (2130253752197328461206964693914292901528724069775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588480314213518676843/100000000000000000000)
  centralHi := (147120078553379669211/25000000000000000000)
  directionLo := (590593356251674669479/100000000000000000000)
  directionHi := (14764833906291866737/2500000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree141.table
  base := (3552452302289893711523607477645378387303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25087418440682094941312244926914442000000000000)
      constant := (960064482826165542902944240132122646184272610475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree141.table
  base := (17762261511445090692587536916611324905621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25093977379051619962739187944668004500000000000)
      constant := (960554144831941211366815567869343079623172397165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590593356251674669479/100000000000000000000)
  centralHi := (14764833906291866737/2500000000000000000)
  directionLo := (592698865091197345011/100000000000000000000)
  directionHi := (148174716272799336253/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree142.table
  base := (45427498463020793465572874216050005478949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265000000000000000000000000000000000000000
      center := (4664)
      previous := (2332)
      next := (2332)
      square := (16667604846740240245872577330000000000000)
      linear := (-2505976214308862197103870681578500000000000)
      constant := (96601082592270599653570457250827650290384297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree142.table
  base := (90854996926023042183161987216260411745739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4770000000000000000000000000000000000000000
      center := (83952)
      previous := (41976)
      next := (41976)
      square := (300016887241324324425706391940000000000000)
      linear := (-45119364974196364057477600978788000000000000)
      constant := (1739706150741362693631010511725940653902717503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592698865091197345011/100000000000000000000)
  centralHi := (148174716272799336253/25000000000000000000)
  directionLo := (594796920731916020679/100000000000000000000)
  directionHi := (14869923018297900517/2500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree143.table
  base := (92920223022533683144032372046925780545321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25443085944641802401090203496434432000000000000)
      constant := (987899598186060570329715178554970898503135047533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree143.table
  base := (92920223022517972717252986848215412671591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-229047641258383162762836481566128575500000000000)
      constant := (8895629215988506519803925294720211840250487840187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594796920731916020679/100000000000000000000)
  centralHi := (14869923018297900517/2500000000000000000)
  directionLo := (596887601767656947787/100000000000000000000)
  directionHi := (149221900441914236947/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree144.table
  base := (47503492923358184028172385397686781267517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-12810459848310828065489591390597213500000000000)
      constant := (500983466649264378096868217023729659411586319441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree144.table
  base := (95006985846703059412200414788557149090367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25627618186871383812436486288687427000000000000)
      constant := (1002477648199038351957677623722447332193920622491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596887601767656947787/100000000000000000000)
  centralHi := (149221900441914236947/25000000000000000000)
  directionLo := (598970985420596870557/100000000000000000000)
  directionHi := (299485492710298435279/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree145.table
  base := (3884611415943369837915166925120352373833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25798753448601509860868162065954422000000000000)
      constant := (1016134120032675301708607114224132554806852102725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree145.table
  base := (6069705337410810778075776906007673261347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-29031185763162718232627533953780638812500000000)
      constant := (1143733444911964058273294911779971546067085141558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598970985420596870557/100000000000000000000)
  centralHi := (299485492710298435279/50000000000000000000)
  directionLo := (4808377180596358887/800000000000000000)
  directionHi := (150261786893636215219/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree146.table
  base := (99245121678133475049584018101661507711611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-25976587200581363590757141350714417000000000000)
      constant := (1030401158388499180457364406393121044499834245703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree146.table
  base := (99245121678123925937635643546228636040431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-233850408528761037410112166662303378000000000000)
      constant := (9278335392501599312115835492414044943078970644067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4808377180596358887/800000000000000000)
  centralHi := (150261786893636215219/25000000000000000000)
  directionLo := (30155808140359650607/5000000000000000000)
  directionHi := (603116162807193012141/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree147.table
  base := (101396494685361504169948067713606299065087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-26154420952561217320646120635474412000000000000)
      constant := (1044768048365999710830518678563522645677616489051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree147.table
  base := (50698247342676708031413330723399978065923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-13080629497345573831066892316353424750000000000)
      constant := (522650129633833315824583318672459880316369345679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30155808140359650607/5000000000000000000)
  centralHi := (603116162807193012141/100000000000000000000)
  directionLo := (24207124176854990867/4000000000000000000)
  directionHi := (151294526105343692919/25000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree148.table
  base := (25892351105066712909611723337632319493317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-6583063676135267762633774980058601750000000000)
      constant := (264808697491294124241427726892358110570987982841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree148.table
  base := (103569404420260001320607210586799043577619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-237052253375679620508295956726419913000000000000)
      constant := (9537968382017910118187389628251135124327868809783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24207124176854990867/4000000000000000000)
  centralHi := (151294526105343692919/25000000000000000000)
  directionLo := (303616522237683989621/50000000000000000000)
  directionHi := (607233044475367979243/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree149.table
  base := (21152770176569783965959138674980990434419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-26510088456520924780424079204994402000000000000)
      constant := (1073801383186029379193600877102947835974175137435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree149.table
  base := (661024068017769488355517021544771603723/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3005696250000000000000000000000000000000000000
      center := (52900254)
      previous := (26450127)
      next := (26450127)
      square := (189048141072939489928748240221192500000000000)
      linear := (-29831646974892364007173481469809772562500000000)
      constant := (1208641692291041157125558882233085318894307939220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303616522237683989621/50000000000000000000)
  centralHi := (607233044475367979243/100000000000000000000)
  directionLo := (609281053812278053921/100000000000000000000)
  directionHi := (304640526906139026961/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree150.table
  base := (107979834073107839602898044370176942765223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-26687922208500778510313058489754397000000000000)
      constant := (1088467828028558392476154432430597209329412924579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree150.table
  base := (107979834073102926235895116651101572679023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-26694899802510911511831082976726272000000000000)
      constant := (1089021978037806387262198666139408021414872611979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609281053812278053921/100000000000000000000)
  centralHi := (304640526906139026961/50000000000000000000)
  directionLo := (611322202088535227993/100000000000000000000)
  directionHi := (305661101044267613997/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree151.table
  base := (110217353991044339888603223966887483682139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-26865755960480632240202037774514392000000000000)
      constant := (1103234124492763731564013367604765422615308123047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree151.table
  base := (110217353991040179016342021531086873108139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-241855020646057495155571641822594715500000000000)
      constant := (9934161174053696614843452620725022485793412389423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611322202088535227993/100000000000000000000)
  centralHi := (305661101044267613997/50000000000000000000)
  directionLo := (306678278900769129951/50000000000000000000)
  directionHi := (613356557801538259903/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree152.table
  base := (28119102659164909604416306377221459904279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-6760897428115121492522754264818596750000000000)
      constant := (279525068144661430450489104822277178857005933267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree152.table
  base := (112476410636656114948084749086110784732713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-243455943069516786704663536854652983000000000000)
      constant := (10068023653468649623426839238667535258704538173141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306678278900769129951/50000000000000000000)
  centralHi := (613356557801538259903/100000000000000000000)
  directionLo := (76923023539559458069/12500000000000000000)
  directionHi := (615384188316475664553/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree153.table
  base := (22951400801991070043465609574147538832787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-27221423464440339699979996344034382000000000000)
      constant := (1133066272286204794681657448394941425150361005755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree153.table
  base := (11475700400995236663597869061461661004941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-13614270305165337680764190660372847250000000000)
      constant := (566821402254728913155632284123145635754928008965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76923023539559458069/12500000000000000000)
  centralHi := (615384188316475664553/100000000000000000000)
  directionLo := (77175644986544271751/12500000000000000000)
  directionHi := (617405159892354174009/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree154.table
  base := (5852956705546670552041757960709853196213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-6849814304105048357467243907198594250000000000)
      constant := (287033030903860366846029443010360964414959079245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree154.table
  base := (117059134110930884730497963049912291805537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-246657787916435369802847326918769518000000000000)
      constant := (10338445935403113745417330338563085187334546632109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77175644986544271751/12500000000000000000)
  centralHi := (617405159892354174009/100000000000000000000)
  directionLo := (19356860553351965043/3125000000000000000)
  directionHi := (619419537707262881377/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree155.table
  base := (23876560187919202668987268074285248652187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-27577090968400047159757954913554372000000000000)
      constant := (1163297826566356325674584599422887309628253786755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree155.table
  base := (119382800939593874313278257622192376014821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-248258710339894661351939221950827785500000000000)
      constant := (10475005737922634851519169584504329396921194939297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19356860553351965043/3125000000000000000)
  centralHi := (619419537707262881377/100000000000000000000)
  directionLo := (621427385882900321593/100000000000000000000)
  directionHi := (310713692941450160797/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree156.table
  base := (121728004495945552809652954287663195635227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-27754924720379900889646934198314367000000000000)
      constant := (1178563381138950009614076278141439843467450503271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree156.table
  base := (2434560089918874835258333794099035964627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-13881090709075219605612839832382558500000000000)
      constant := (589581369341316085632299955332861051894432236775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621427385882900321593/100000000000000000000)
  centralHi := (310713692941450160797/50000000000000000000)
  directionLo := (155857191877097650439/25000000000000000000)
  directionHi := (623428767508390601757/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree157.table
  base := (124094744779984583713528757701260838877449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-27932758472359754619535913483074362000000000000)
      constant := (1193928787333223201636854179316157423292904681677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree157.table
  base := (124094744779983050423658044369069873566513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-251460555186813244450123012014944320500000000000)
      constant := (10750822666066283978711366380680272152176598799741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155857191877097650439/25000000000000000000)
  centralHi := (623428767508390601757/100000000000000000000)
  directionLo := (625423744663413607303/100000000000000000000)
  directionHi := (78177968082926700913/12500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree158.table
  base := (3162075544792894543647475434990598922099/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-3513824028042451043678111595979294625000000000)
      constant := (151174255643647077076858134272553918429069780635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree158.table
  base := (126483021791714483666479771069726155452611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-253061477610272535999214907047002588000000000000)
      constant := (10890079791690424615827538561500247232614163948327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625423744663413607303/100000000000000000000)
  centralHi := (78177968082926700913/12500000000000000000)
  directionLo := (25096495137626931033/4000000000000000000)
  directionHi := (313706189220336637913/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree159.table
  base := (1031142684249135304507194846760742382829/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (887216)
      previous := (443608)
      next := (443608)
      square := (3170618718204435889790326880020000000000000)
      linear := (-533743886345650227911582491558384000000000000)
      constant := (23112436878996433841329731545177215981480123625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree159.table
  base := (32223208882785203539142201730368727007161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (221804)
      previous := (110902)
      next := (110902)
      square := (792654679551108972447581720005000000000000)
      linear := (-133470859556463221985485745324455375000000000)
      constant := (5781046134704464423355031260167078319249348601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25096495137626931033/4000000000000000000)
  centralHi := (313706189220336637913/50000000000000000000)
  directionLo := (629394728967726944829/100000000000000000000)
  directionHi := (62939472896772694483/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree160.table
  base := (131324185998265808587773931193985267477309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-28466259728299315809202851337354347000000000000)
      constant := (1240624115646127088909541424425138645867715077457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree160.table
  base := (32831046499566219582498993298817706430079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-64065830614297779774349674277779780750000000000)
      constant := (2792822841510842827721289693789677440220391470003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629394728967726944829/100000000000000000000)
  centralHi := (62939472896772694483/10000000000000000000)
  directionLo := (15784271385704946017/2500000000000000000)
  directionHi := (631370855428197840681/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree161.table
  base := (133777073193090342701722534351321402762759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-28644093480279169539091830622114342000000000000)
      constant := (1256388928327125670529511083008136862327834610307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree161.table
  base := (26755414638617911048240619342975806028909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-257864244880650410646490592143177390500000000000)
      constant := (11313245814772191112049327429561892405415401691565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15784271385704946017/2500000000000000000)
  centralHi := (631370855428197840681/100000000000000000000)
  directionLo := (633340816082391880853/100000000000000000000)
  directionHi := (316670408041195940427/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree162.table
  base := (68125748557809207816918274562661118364479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-14410963616129511634490404953437168500000000000)
      constant := (636126796314903756656579096714790467226792947867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree162.table
  base := (27250299423123549815297878974336603727213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-28829463033789966910620276352803962000000000000)
      constant := (1272899930133620500726155632764589588325553394245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633340816082391880853/100000000000000000000)
  centralHi := (316670408041195940427/50000000000000000000)
  directionLo := (317652334143669554067/50000000000000000000)
  directionHi := (127060933657467821627/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree163.table
  base := (138747457765852938936642833170826933701851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-28999760984238876998869789191634332000000000000)
      constant := (1288218108554173395148706013829687206295424637223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree163.table
  base := (138747457765852374741025551014414144821259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-261066089727568993744674382207293925500000000000)
      constant := (11599852035334558503399011073957926846907097077263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317652334143669554067/50000000000000000000)
  centralHi := (127060933657467821627/20000000000000000000)
  directionLo := (318631234258139630693/50000000000000000000)
  directionHi := (637262468516279261387/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree164.table
  base := (141264955143796823556791256906996062803119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-29177594736218730728758768476394327000000000000)
      constant := (1304282476100224093762503830037954064587297712587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree164.table
  base := (141264955143796346021408257537463298241673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-262667012151028285293766277239352193000000000000)
      constant := (11744503807168120109006116149665533435530102503861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318631234258139630693/50000000000000000000)
  centralHi := (637262468516279261387/100000000000000000000)
  directionLo := (639214272377610210859/100000000000000000000)
  directionHi := (31960713618880510543/5000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree165.table
  base := (71901994624726485038168346423316723721529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-14677714244099292229323873880577161000000000000)
      constant := (660223347633980192055880494254122422620602067517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree165.table
  base := (35950997312363141476307825738203175673271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 667932500000000000000000000000000000000000000
      center := (11755612)
      previous := (5877806)
      next := (5877806)
      square := (42010698016208775539721831160265000000000000)
      linear := (-7340775960402432690079393674205846125000000000)
      constant := (330279296852868786215440429981309236136186082883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639214272377610210859/100000000000000000000)
  centralHi := (31960713618880510543/5000000000000000000)
  directionLo := (320580067316658622437/50000000000000000000)
  directionHi := (5129281077066537959/800000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree166.table
  base := (73182280041412130385638941638851994585513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1335865000000000000000000000000000000000000000
      center := (23511224)
      previous := (11755612)
      next := (11755612)
      square := (84021396032417551079443662320530000000000000)
      linear := (-14766631120089219094268363522957158500000000000)
      constant := (668355383028691518131401450606930997449395264749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree166.table
  base := (7318228004141195935298878240492961470419/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6011392500000000000000000000000000000000000000
      center := (105800508)
      previous := (52900254)
      next := (52900254)
      square := (378096282145878979857496480442385000000000000)
      linear := (-66467214249486717097987516825867182000000000000)
      constant := (3009126168485008505786101127633567283881506496915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320580067316658622437/50000000000000000000)
  centralHi := (5129281077066537959/800000000000000000)
  directionLo := (321550054608450243591/50000000000000000000)
  directionHi := (643100109216900487183/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree167.table
  base := (1163645840968074634297197532545154596493/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-3713886999019786489803213291334289000000000000)
      constant := (169134336058561601709426913709311913541328688624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree167.table
  base := (148946667643913263697736662660747997955129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24045570000000000000000000000000000000000000000
      center := (423202032)
      previous := (211601016)
      next := (211601016)
      square := (1512385128583515919429985921769540000000000000)
      linear := (-267469779421406159941041962335526995500000000000)
      constant := (12183853768878400142459290356608390751672116122853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321550054608450243591/50000000000000000000)
  centralHi := (643100109216900487183/100000000000000000000)
  directionLo := (645034249250817048669/100000000000000000000)
  directionHi := (64503424925081704867/10000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree168.table
  base := (151550311932723675002134835036390774601931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-29888929744138145648314685615434307000000000000)
      constant := (1369538462501290471826543658616999193422721711063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree168.table
  base := (151550311932723430011513894964749033170219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (47022448)
      previous := (23511224)
      next := (23511224)
      square := (168042792064835102158887324641060000000000000)
      linear := (-29896744649429494610014873040842807000000000000)
      constant := (1370233552390931273834141747221869366939186920887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell168.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645034249250817048669/100000000000000000000)
  centralHi := (64503424925081704867/10000000000000000000)
  directionLo := (646962607063453871821/100000000000000000000)
  directionHi := (323481303531726935911/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree169.table
  base := (2408992077332147186049567659971759460901/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 333966250000000000000000000000000000000000000
      center := (5877806)
      previous := (2938903)
      next := (2938903)
      square := (21005349008104387769860915580132500000000000)
      linear := (-3758345437014749922275458112524287750000000000)
      constant := (173262761019472094639661858039860878522015922984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree169.table
  base := (77087746474628606292318834452400560037593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12022785000000000000000000000000000000000000000
      center := (211601016)
      previous := (105800508)
      next := (105800508)
      square := (756192564291757959714992960884770000000000000)
      linear := (-135335812134162371519612876199821765250000000000)
      constant := (6240624640929992354937239099245077761981377011301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell168.Kernel169
