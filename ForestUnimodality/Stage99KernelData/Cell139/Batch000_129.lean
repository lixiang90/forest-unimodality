import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell139.Parameters
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch000_049
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch050_099
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch100_149
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel000
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
  base := (890811085250096275362921/16000000000000000000000)
  polynomial :=
    { denominator := 7526000000000000000000000000000000000000000
      center := (47787)
      previous := (0)
      next := (42525)
      square := (1110654263135287407204820900220000000000000)
      linear := (-5124156772350891993594856905380000000000000)
      constant := (419015264224514035523833965375000000000000000) }

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
  base := (890811085250096275362921/16000000000000000000000)
  polynomial :=
    { denominator := 15052000000000000000000000000000000000000000
      center := (95599)
      previous := (0)
      next := (85025)
      square := (2221308526270574814409641800440000000000000)
      linear := (-10248313544701783987189713810760000000000000)
      constant := (838030528449028071047667930750000000000000000) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel001
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
  base := (334231037752820695445961594637816255354013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-118525524368634524246194222824230175000000000000)
      constant := (4789632915360270040790482341904697255822478908197) }

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
  base := (334173071983674230120623885819331447133621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-2133563562472590369625921462795538775000000000000)
      constant := (86198913282257223337934893999479008514960750955082) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel002
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
  base := (209726127760626247085638173407580961638097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-140640039065487015632901212973735650000000000000)
      constant := (3095188789212382572673471591040305929227970358393) }

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
  base := (8386458644171259144141916396689335546689/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-506345790170620829556214547489206590000000000000)
      constant := (11139523569166539787600085445705933391119126739690) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel003
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
  base := (138470560582452094533675243021665014204287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-162754553762339507019608203123241125000000000000)
      constant := (2166465861386383897581642997544632289082604444503) }

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
  base := (5536613198269093226952576050668430983051/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-65108763094080398354138311379922825000000000000)
      constant := (866300548045887690336569846101249174504632956190) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel004
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
  base := (48176743657847684143945246155115704292151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-184869068459191998406315193272746600000000000000)
      constant := (1662050436687952843479149166442196649661767067038) }

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
  base := (96310297784520876022626363491782627820251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-3328059727614131704091375286747021300000000000000)
      constant := (29907742000618930254515203740785639044079404083542) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel005
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
  base := (35178746622853408941879170082967259711421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-206983583156044489793022183422252075000000000000)
      constant := (1397613722814569248064979364429777814523725180298) }

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
  base := (14064908901887933002579273553823389750359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-745245023198929096449305312279503095000000000000)
      constant := (5030245494633085117983293869753720976729372512078) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel006
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
  base := (53428683869661913052058962529424258429193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-229098097852896981179729173571757550000000000000)
      constant := (1273271381498066785381365384676712503307047413617) }

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
  base := (26701660568525829018855406106553732471577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-458265611597239917822408648449778850000000000000)
      constant := (2546205021717461417119424090969427515638272066052) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel007
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
  base := (41723896543284355966789453248735815800031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-251212612549749472566436163721263025000000000000)
      constant := (1234603580201006195517773481580039327143809165239) }

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
  base := (834076186144181393806703907420211257971/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-904511178551134607711365822139700765000000000000)
      constant := (4444425186801238526591709826805131172299202277820) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel008
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
  base := (8283053042051761942646370958704883685921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-273327127246601963953143153870768500000000000000)
      constant := (1251719347745181734614217869163300496471937122596) }

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
  base := (33115699327207827945550951910453358882829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-4920721281136186816711980385348998000000000000000)
      constant := (22532187534774046142992857647880087861173177085818) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel009
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
  base := (6620007232099901632794350265165412104153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-295441641943454455339850144020273975000000000000)
      constant := (1308000284076896285375213704160585707460308327428) }

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
  base := (413530306274624630004615857680993070649/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-590987407724077843874125739999943575000000000000)
      constant := (2616337670964874176675900926002862145463253799168) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel010
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
  base := (21103093644329683608861015213544347192233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-317556156640306946726557134169779450000000000000)
      constant := (1394040451915184450095629550231749326486694767377) }

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
  base := (21090688309092706589366113681851833668113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-5717052057897214373022282934649986350000000000000)
      constant := (25097478422936077220091074411722834761731659839746) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel011
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
  base := (8307845953778630248073193845223200608523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-339670671337159438113264124319284925000000000000)
      constant := (1504378070050800540346280110958386828237677040774) }

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
  base := (8302255585192648070503573845038923390319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-6115217446277728151177434209300480525000000000000)
      constant := (27085265025913077641910226976841669886290170140796) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel012
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
  base := (12785869947998866183959239148543884964629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-361785186034011929499971114468790400000000000000)
      constant := (1635728633899175462532073057292902490015705662301) }

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
  base := (1596954288204738234510886333980007169827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-723709203850915769925842831550108300000000000000)
      constant := (3272369290674585042907934283378385268835392332208) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel013
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
  base := (2366936785129499696834390049925490492849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-383899700730864420886678104618295875000000000000)
      constant := (1786026449154550701893127777719720432709040525924) }

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
  base := (9458287698722732624225908805685046773809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-6911548223038755707487736758601468875000000000000)
      constant := (32158499888267596920030911815939295160151973846978) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel014
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
  base := (6564613881404531353931067034517662294391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-406014215427716912273385094767801350000000000000)
      constant := (1953902091484467833772709306299730812823504312079) }

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
  base := (655582728941973560474238942102823708559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-1461942722283853897128577606650392610000000000000)
      constant := (7036432182088391411988930891143122392879478712956) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel015
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
  base := (4008663424004350767577357819322436883013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-428128730124569403660092084917306825000000000000)
      constant := (2138395405896964431900841401622277085817797309197) }

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
  base := (4000483810715906235595099357906782963787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-856430999977753695977559923100273025000000000000)
      constant := (4278337049518217769438867712875935023058339600006) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel016
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
  base := (174973661168223881374609630236184247431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-90048648964284379009359815013362460000000000000)
      constant := (467759226051437667001579249347137957717521551678) }

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
  base := (1742118731956857180404751581977755758543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-8106044388180297041953190582552951400000000000000)
      constant := (42114338032719005020103746751338220764070457327806) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel017
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
  base := (-251030108201965359652344327868360226117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-472357759518274386433506065216317775000000000000)
      constant := (2554553950091814469241100722842137748507805066227) }

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
  base := (-258120646583380909371512737924016208921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-8504209776560810820108341857203445575000000000000)
      constant := (46000171777311024711451104335816085272094157982318) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel018
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
  base := (-2024873279825136229957127866074994705287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-494472274215126877820213055365823250000000000000)
      constant := (2785226550656322326109545600289891039549030886497) }

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
  base := (-2031465464880058167644179969141273916799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-989152796104591622029277014650437750000000000000)
      constant := (5572730487941999937794430005367684606050668441938) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel019
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
  base := (-719517914561831392307865409322571176119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-103317357782395873841384009103065745000000000000)
      constant := (606089729349845774781496342089838731944126195889) }

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
  base := (-900927468559499152200537489269529247571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-9300540553321838376418644406504433925000000000000)
      constant := (54570971383469547901904033325187522679415779636072) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel020
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
  base := (-4990894383262000789507802901414017656853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-538701303608831860593627035664834200000000000000)
      constant := (3289912744691743269378290847710373046009977511843) }

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
  base := (-2498284082857667000780616929212694943327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-9698705941702352154573795681154928100000000000000)
      constant := (59243828148725898543368215785336267858153593278532) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel021
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
  base := (-777913538263014470870243489630063241177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-560815818305684351980334025814339675000000000000)
      constant := (3563356589729811426534364640666380682756467368696) }

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
  base := (-1557140106708064850954926829041896824731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1121874592231429548080994106200602475000000000000)
      constant := (7129824914555755482338910089590778113831215283688) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel022
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
  base := (-3655383702829547687622083239972217163603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-582930333002536843367041015963845150000000000000)
      constant := (3850554524499416390992596296338713330567361742186) }

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
  base := (-7315622382742282875906745911573268426311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-10495036718463379710884098230455916450000000000000)
      constant := (69340697884193647733795654594623879590744299481938) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel023
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
  base := (-1033383265216406122193430610992636106487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-605044847699389334753748006113350625000000000000)
      constant := (4151311217401668815241890749135622208875636669576) }

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
  base := (-8271548093974344196322204953156927441417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-10893202106843893489039249505106410625000000000000)
      constant := (74757133236192295421825757832662874781139608249486) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel024
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
  base := (-9104194197806145788132217309304954007173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-627159362396241826140454996262856100000000000000)
      constant := (4465456891642546390147123041220966178721203107763) }

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
  base := (-9108326798850020931457301538617092442057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1254596388358267474132711197750767200000000000000)
      constant := (8934963825940341748975527793832241839463700344734) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel025
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
  base := (-9832603014763937332287874000973521816279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-649273877093094317527161986412361575000000000000)
      constant := (4792843553902502801364587632649556930618802408849) }

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
  base := (-2459102306592942528916317220529945018757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-11689532883604921045349552054407398975000000000000)
      constant := (86310657762406724816267380945943713096887125124824) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel026
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
  base := (-10461422341843251107732107566206252217429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-671388391789946808913868976561867050000000000000)
      constant := (5133341925106188082198554881869190560994580614499) }

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
  base := (-10464924358402159632073567494305516295849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-12087698271985434823504703329057893150000000000000)
      constant := (92442756400355748520305622628336553782258434907342) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel027
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
  base := (-2749660118504538969823283708467280513081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-693502906486799300300575966711372525000000000000)
      constant := (5486838889646747568321435982614480759419965317244) }

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
  base := (-5500929795996203414418373740038505621199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1387318184485105400184428289300931925000000000000)
      constant := (10978770499472452305043741152754408526366738709476) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel028
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
  base := (-5725628071347749005892101547732553341809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-715617421183651791687282956860878000000000000000)
      constant := (5853235344304674707450439699798953130756939588558) }

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
  base := (-1145421267896906791948916970856004389509/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-2576805809749292475963001175671776300000000000000)
      constant := (21081481687764595557488376943090907906973186387244) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel029
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
  base := (-5912703954768117939694725169371657514299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-737731935880504283073989947010383475000000000000)
      constant := (6232444366009433408305153402396760363137312486938) }

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
  base := (-11828121147641555193328872616719010315657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-13282194437126976157970157153009375675000000000000)
      constant := (112236613879182605524921797568884731661047213611406) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel030
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
  base := (-1515810641978978627739741497221713299693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-759846450577356774460696937159888950000000000000)
      constant := (6624389640494334545545218638014306854904395775064) }

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
  base := (-12128973296830784792978151492544115443739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1520039980611943326236145380851096650000000000000)
      constant := (13255019714481808204241659161672782623847291536218) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel031
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
  base := (-12359223600801684408456547212411591765727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-781960965274209265847403927309394425000000000000)
      constant := (7029004108325284628408587138295676627100797272137) }

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
  base := (-12361503834818868827165411283069778698739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-14078525213888003714280459702310364025000000000000)
      constant := (126581892295434055398743558769257493695279852115962) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel032
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
  base := (-782986760507107604791035749434298800301/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-804075479971061757234110917458899900000000000000)
      constant := (7446228794328883954947698072747422393459849426096) }

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
  base := (-12529876562509592838276508671754530982563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-14476690602268517492435610976960858200000000000000)
      constant := (134095697192235310998268749422236140465881093603354) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel033
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
  base := (-631792221531211865890755502083860223467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-165237998933582849724163581521681075000000000000)
      constant := (1575202358618160434826335484673280066065818056308) }

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
  base := (-12637756031139486654338484896276792709779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1652761776738781252287862472401261375000000000000)
      constant := (15759517565419256561406581698341340345934372814698) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel034
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
  base := (-12686620920172736431091246649995256164787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-848304509364766740007524897757910850000000000000)
      constant := (8318307388054570012880070784625955954758324230997) }

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
  base := (-793023110116124240087827219192059201001/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-15273021379029545048745913526261846550000000000000)
      constant := (149800952344639361578490123523919771825801410799328) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel035
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
  base := (-6341481603698664270383129633083768690581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-870419024061619231394231887907416325000000000000)
      constant := (8773075285459050402488545664294453414931428663622) }

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
  base := (-3171140588162718647885714782303839489753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-15671186767410058826901064800912340725000000000000)
      constant := (157990854920045586357430346656148805134819360125496) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel036
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
  base := (-12627381009723721217141863954166612591503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-892533538758471722780938878056921800000000000000)
      constant := (9240279947281353078817050381916026386546789555993) }

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
  base := (-1578605323904852768562252319507213864851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1785483572865619178339579563951426100000000000000)
      constant := (18489414040838445048562184865737884241773066882896) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel037
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
  base := (-6261044629036074727716027703187521098853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-914648053455324214167645868206427275000000000000)
      constant := (9719890009725324188813640581481434801660851627686) }

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
  base := (-12523424524920751515172801694655772912269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-16467517544171086383211367350213329075000000000000)
      constant := (175042002364029937948840699936494443839290928157702) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel038
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
  base := (-96633155737813838552248474588960919689/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-936762568152176705554352858355932750000000000000)
      constant := (10211877775755317352491639152252305135129466567552) }

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
  base := (-1237026329988487624820574230908480957703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-3373136586510320032273303724972764650000000000000)
      constant := (36780436915177875463382357262100409620428172054948) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel039
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
  base := (-243399467535327178947627921088230444469/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-191775416569805839388211969701087645000000000000)
      constant := (2143243754362806655480590984775869657766238447390) }

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
  base := (-12171086466698710482944882601748176513601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-1918205368992457104391296655501590825000000000000)
      constant := (21442759186642274079119712687596758219782408082862) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel040
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
  base := (-11926405649788913173805698854441393802547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-980991597545881688327766838654943700000000000000)
      constant := (11232891360246536098326692094365396463160381849557) }

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
  base := (-5963710675472515862730410846810906971929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-17662013709312627717676821174164811600000000000000)
      constant := (202289557386312543380781135799383897814431455743964) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel041
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
  base := (-1454961562207098979475246347303533156907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1003106112242734179714473828804449175000000000000)
      constant := (11761876400127231811331706564483634623671246901736) }

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
  base := (-11640619004967933279733366734816461295703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-18060179097693141495831972448815305775000000000000)
      constant := (211816014335154243590972747190547693709057207831474) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel042
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
  base := (-11311030323303862619479991613961552937517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1025220626939586671101180818953954650000000000000)
      constant := (12303156950188384754159044899889012532152312839627) }

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
  base := (-1131187518590655669234184013496111433647/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-410185433023859006088602749410351110000000000000)
      constant := (4923642194401965549510922799373271180651904774628) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel043
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
  base := (-5470739289538280829713554132345505180431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1047335141636439162487887809103460125000000000000)
      constant := (12856718008405721944595243523164222962071943094322) }

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
  base := (-170972636635016387342429165773133519669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-18856509874454169052142274998116294125000000000000)
      constant := (231532940741981805591259568741563375816645550601728) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel044
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
  base := (-10531975901216055292104542686263032560331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1069449656333291653874594799252965600000000000000)
      constant := (13422546283531438942558900669470802455493210344061) }

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
  base := (-2106535551671698689381789702294101280711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-3850935052566936566059485254553357660000000000000)
      constant := (48344580243373447287949342974576921659416284397138) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel045
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
  base := (-10083354276227169948550177988643339266893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1091564171030144145261301789402471075000000000000)
      constant := (14000629994496021686470853068569390836818959015083) }

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
  base := (-1008399369485542639515058415933717262401/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-436729792249226591298946167720384055000000000000)
      constant := (5602968183237854137979174921526267780720987976924) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel046
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
  base := (-9596351488829767761985269614969190032151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1113678685726996636648008779551976550000000000000)
      constant := (14590958694143151310867987228992994620601626406481) }

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
  base := (-9596933858338681099895538311707995937533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-20051006039595710386607728822067776650000000000000)
      constant := (262764753902151287788396400829065540607842946984614) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel047
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
  base := (-1814324413634182770340639318981637787451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-227158640084769825606943153940296405000000000000)
      constant := (3038704622845897989561420748620092903845407760781) }

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
  base := (-9072152333454157918056849254127334362049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-20449171427976224164762880096718270825000000000000)
      constant := (273616291471126518601948422026353069125731071526942) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel048
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
  base := (-1701949384101572033251456239596164092119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-231581543024140323884284551970197500000000000000)
      constant := (3161663005804852350444221652408785384703863391889) }

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
  base := (-8510229615792815012273294013154428696027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-2316370757372970882546447930152085000000000000000)
      constant := (31632003666016337516170092536095055733131616102874) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel049
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
  base := (-7911241811999905956817437299838562915879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1180022229817554110808129750000492975000000000000)
      constant := (16435327135191486565791861357628711915456520576449) }

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
  base := (-1977920273135396454737037655101763123897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-21245502204737251721073182646019259175000000000000)
      constant := (295979847107758831502221652181102327719952088981304) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel050
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
  base := (-7276564844016909615864182412813438939429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1202136744514406602194836740149998450000000000000)
      constant := (17074552945938348062175770572672738470396504596499) }

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
  base := (-909620564463616454438557223535776050369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-21643667593117765499228333920669753350000000000000)
      constant := (307491617138737501946793409695025016813734632460016) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel051
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
  base := (-6606123045011178573463858873534203795123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1224251259211259093581543730299503925000000000000)
      constant := (17725986697673173759723140818477488523543116944213) }

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
  base := (-6606486591987543024783180594284012193037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-2449092553499808808598165021702249725000000000000)
      constant := (35469248824938223805491951846884512519978320913494) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel052
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
  base := (-5900278187104579376354127523112668061087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1246365773908111584968250720449009400000000000000)
      constant := (18389623267641578539536720418868136689214105756297) }

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
  base := (-2950304398708472079286496086195467191329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-22439998369878793055538636469970741700000000000000)
      constant := (331174621830765804376983036775869950593825736914364) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel053
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
  base := (-5159351921769634458682146462117820986189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16964385)
      previous := (0)
      next := (15096375)
      square := (394282263413027029557711419578100000000000000)
      linear := (-23933590351037058044433164350915375000000000000)
      constant := (359725624551025516699862155552281265726156926303) }

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
  base := (-1289913127807958783325091601888633507849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (305438805)
      previous := (0)
      next := (271654875)
      square := (7097080741434486532038805552405800000000000000)
      linear := (-430908750155835977994222410275872375000000000000)
      constant := (6478220423463884836545772956524378088532387056856) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel054
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
  base := (-175345212681503168982633013353213862779/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-258118960660363313548332940149604070000000000000)
      constant := (3950697429517965501157993879642043101299532751745) }

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
  base := (-1095975887833301390787019207675208927667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-2581814349626646734649882113252414450000000000000)
      constant := (39526260934752025315731449413351930083916412034216) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel055
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
  base := (-35733678682956775908463755462952602829/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-262541863599733811825674338179505165000000000000)
      constant := (4090741360620062104823694476196683315911529637980) }

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
  base := (-1786808091723121061848672711564460174893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-23634494535020334390004090293922224225000000000000)
      constant := (368346554930291286975064261872325169923852090270988) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel056
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
  base := (-2728791045724434338421717739315057100399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1334823832695521550515078681047031300000000000000)
      constant := (21166113860879772031875380664582318847213700192569) }

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
  base := (-2729016667015600124208830679036743798013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-24032659923400848168159241568572718400000000000000)
      constant := (381176244326459538761503810744341121860987813004454) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel057
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
  base := (-231262679198416822983921527873708321409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1356938347392374041901785671196536775000000000000)
      constant := (21890705466460973339280943539476974900159637935032) }

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
  base := (-1850306393049243769798786931146156861469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-2714536145753484660701599204802579175000000000000)
      constant := (43802818363346693537563838718693933454813428743478) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel058
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
  base := (-234369627440561288395391552258563415337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1379052862089226533288492661346042250000000000000)
      constant := (22627479078406832090714038369077099222616443552188) }

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
  base := (-468832331148777649830305096409127102619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-24828990700161875724469544117873706750000000000000)
      constant := (407493872060552705896988090641841859168164646226004) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel059
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
  base := (8917892042115382772339164297663221507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1401167376786079024675199651495547725000000000000)
      constant := (23376432433445020934454623764528989629084123554683) }

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
  base := (1749770758409197521254547010765127437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-5045431217708477900524939078504840185000000000000)
      constant := (84196344800042538432873581804532504923834910223354) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel060
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
  base := (197789080025359458831221200224456382621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-284656378296586303212381328329010640000000000000)
      constant := (4827512703113644385037750074488145415311042022949) }

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
  base := (494395966045405241306350144480041317611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-2847257941880322586753316296352743900000000000000)
      constant := (48298764982092944686901842483285610271237417745036) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel061
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
  base := (2002477169969128552090545991460164133353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1445396406179784007448613631794558675000000000000)
      constant := (24910870528636557302661580073360178332458517016657) }

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
  base := (1001168932023750680694045222096453924949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-26023486865303417058934997941825189275000000000000)
      constant := (448615322280563149295678070157597768107138931629716) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel062
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
  base := (762350041984710052597269059254719992653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1467510920876636498835320621944064150000000000000)
      constant := (25696351872074719775079658947915012777824580953428) }

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
  base := (3049273740418315076140160804861518026007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-26421652253683930837090149216475683450000000000000)
      constant := (462761007546741102937140683125556660481331499273294) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel063
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
  base := (4129613648245972252888792386704178224149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1489625435573488990222027612093569625000000000000)
      constant := (26494006119305297470110877538962900480722569721181) }

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
  base := (412949892915434956470425042955848567443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-595995947601432102561006677580581725000000000000)
      constant := (10602798110843724805691995985951170237419853111468) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel064
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
  base := (1310756950207395644066084709989545133821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1511739950270341481608734602243075100000000000000)
      constant := (27303831998602649547272933349214845389312131902996) }

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
  base := (2621461862079980403167636004376059581021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-27217983030444958393400451765776671800000000000000)
      constant := (491710021739680145561718859924326735555967755891764) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel065
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
  base := (1277912510109529323327275221296929250033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-306770892993438794599088318478516115000000000000)
      constant := (5625165675217846447947828727175975775174010535577) }

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
  base := (3194734072643331198972183867805824868453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-27616148418825472171555603040427165975000000000000)
      constant := (506513307416295145027762878521018410378862350948052) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel066
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
  base := (189228662258822535557009688263958391649/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-311193795932809292876429716508417210000000000000)
      constant := (5791998848125837702625130080333923345727744229448) }

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
  base := (7569060872251491633606205316401007447671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3112701534133998438856750479453073350000000000000)
      constant := (57948417093275770757668119448665488677583560032798) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel067
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
  base := (4390857966589364316753007765004874018659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1578083494360898955768855572691591525000000000000)
      constant := (29806328690402891937200735395550107430418341186742) }

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
  base := (1097704787150996823578032430479445314369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-28412479195586499727865905589728154325000000000000)
      constant := (536777344796679116592569120178089007516123386243984) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel068
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
  base := (10027214069049847326004237501988546484963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1600198009057751447155562562841097000000000000000)
      constant := (30664830920971491648253706649240170329291432038747) }

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
  base := (2005428736497668676138451115850681663329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-5762128916793402701204211372875729700000000000000)
      constant := (110447613165283465537047778542243189052622915366818) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel069
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
  base := (11305590215506129550254864410837634693177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1622312523754603938542269552990602475000000000000)
      constant := (31535500214662786898757734817082953915378149466913) }

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
  base := (11305526411609028545328503748728712082639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3245423330260836364908467571003238075000000000000)
      constant := (63101989336379251396544109838168343822266270411982) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel070
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
  base := (6308399575405811907959000310935586907641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1644427038451456429928976543140107950000000000000)
      constant := (32418335931129354142233805109448944448702767902658) }

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
  base := (12616741323015039696414376443186054179873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-29606975360728041062331359413679636850000000000000)
      constant := (583816847888752403843648737322608429364467845413666) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel071
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
  base := (13960800520638647599328665606524241773907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1994390000000000000000000000000000000000000000
      center := (12663555)
      previous := (0)
      next := (11269125)
      square := (294323379730851162909277538558300000000000000)
      linear := (-23472416241525477765009627229431175000000000000)
      constant := (469201936604888641024908097220731736692646238173) }

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
  base := (436273378664263627444189819212375990917/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35899020000000000000000000000000000000000000000
      center := (228003615)
      previous := (0)
      next := (202784625)
      square := (5297820835155320932366995694049400000000000000)
      linear := (-422607616184627532964598742089156775000000000000)
      constant := (8449787142799836051872569289252553121794187444288) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel072
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
  base := (3834389577497315119308376352477962087549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1688656067845161412702390523439118900000000000000)
      constant := (34220504408137547639316545174933990647741146543124) }

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
  base := (15337510829362350301655163084875415158003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3378145126387674290960184662553402800000000000000)
      constant := (68474668067851105551700295072850297395164968365014) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel073
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
  base := (418676009326538640592705630143988839183/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-342154116508402780817819502717724875000000000000)
      constant := (7027967240702145747819796866057836953188060815416) }

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
  base := (8373498679561478646670849423727053152689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-30801471525869582396796813237631119375000000000000)
      constant := (632828216122568045637704414149092710896287375599876) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel074
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
  base := (18189218014601581574646681576429433015491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1732885097238866395475804503738129850000000000000)
      constant := (36071332478736991786271321944005545069323532177979) }

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
  base := (18189179052823050874092859985403289672027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-31199636914250096174951964512281613550000000000000)
      constant := (649603490371166550347550890160906527071538424066134) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel075
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
  base := (19664065617017443469152069894460261114779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1754999611935718886862511493887635325000000000000)
      constant := (37014992871066905751767957770998238562731899037651) }

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
  base := (9832015165353084570477432334191023025621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3510866922514512217011901754103567525000000000000)
      constant := (74066425426289924829540012776974722633083988759796) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel076
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
  base := (21171560308180958992937647301907004200841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1777114126632571378249218484037140800000000000000)
      constant := (37970817056627270325957470417939220576767618502129) }

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
  base := (10585764177548711843300655388804529144057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-31995967691011123731262267061582601900000000000000)
      constant := (683811225697960317228362200185740413325729808762788) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel077
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
  base := (2271168166541667568116838150346643391861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-359845728265884773927185094837329255000000000000)
      constant := (7787760949245909933957265854081307898335469969018) }

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
  base := (11355826367343377080065774033888778439679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-32394133079391637509417418336233096075000000000000)
      constant := (701243675757820393087616000565508420321270044047036) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel078
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
  base := (3035551431460584973056441275479549356229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1821343156026276361022632464336151750000000000000)
      constant := (39918955681634176544817709450125268880674350741608) }

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
  base := (24284385260981355968587964596258646627733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3643588718641350143063618845653732250000000000000)
      constant := (79877241597239279419317434247009304711044958733754) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel079
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
  base := (2588973338041251084612902572733346404023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-368691534144625770481867890897131445000000000000)
      constant := (8182253926444106496047903108718858856845515919774) }

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
  base := (25889709673384483617781917349469171339893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-33190463856152665065727720885534084425000000000000)
      constant := (736765717405409319060226328505312257389612393794506) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel080
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
  base := (5505526581165683711229495985518397231449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-373114437083996268759209288927032540000000000000)
      constant := (8383149278403606251247117835127696257406449954881) }

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
  base := (27527611449754693489214632460769866777347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-33588629244533178843882872160184578600000000000000)
      constant := (754855301147140218442969806455794847306144940049574) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel081
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
  base := (29198097035999725319279841271084847538523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1887686700116833835182753434784668175000000000000)
      constant := (42932385777058710521435001703171376793547219690387) }

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
  base := (1824879851228185857231194821139480796047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-3776310514768188069115335937203896975000000000000)
      constant := (85907102477155639081757846818765840592648211662176) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel082
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
  base := (30901114166091454050855166227686235921801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1909801214813686326569460424934173650000000000000)
      constant := (43961187623016145783207685256416942710876572944369) }

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
  base := (30901096597780479882662097681749207143673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-34384960021294206400193174709485566950000000000000)
      constant := (791691577894296236293559628112023940675992505293266) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel083
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
  base := (32636673929636365513610757308973901151619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1931915729510538817956167415083679125000000000000)
      constant := (45002151783099409000990568941543244433458719663611) }

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
  base := (6527331607088292574735901257784003179707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-6956625081934944035669665196827212225000000000000)
      constant := (162087653061823617910134369624339679243287642828694) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel084
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
  base := (34404767065852260560489026234918755137273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1954030244207391309342874405233184600000000000000)
      constant := (46055278126174259162669661455772650749013403879137) }

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
  base := (6880950537599715314652147506099905844241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-781806462179005199033410605750812340000000000000)
      constant := (18431199604057011829078181168081963447777080473458) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel085
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
  base := (18102692650629738847816906888982165584101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1976144758904243800729581395382690075000000000000)
      constant := (47120566535086826043400846784752052631876207746138) }

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
  base := (7241074459328945158532971278316272059911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-7115891237287149546931725706687409895000000000000)
      constant := (169717745281921737770841737554294032452135971929262) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel086
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
  base := (19019260622022078046990923068024688776519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-1998259273601096292116288385532195550000000000000)
      constant := (48198016905167776157358749535750990209745824543422) }

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
  base := (38038509482896159062994559180309806768699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-35977621574816261512813779808087543650000000000000)
      constant := (867992496109597175265778940594465805504763191502358) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel087
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
  base := (19952084144891928386878727644186381463437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2020373788297948783502995375681701025000000000000)
      constant := (49287629142897371621169238329507023947103970481706) }

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
  base := (1995207882721922232760026643104996543729/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56640676000000000000000000000000000000000000000
      center := (359739037)
      previous := (0)
      next := (319949075)
      square := (8358783984356173026623482095055720000000000000)
      linear := (-808350821404372784243754024060845285000000000000)
      constant := (19724784213383596341413944496853556105335198241608) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel088
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
  base := (2612645033581501440039807519628799241469/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2042488302994801274889702365831206500000000000000)
      constant := (50389403164713983413540607937071746632420365572176) }

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
  base := (41802310921092774041243233043576687915339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-36773952351577289069124082357388532000000000000000)
      constant := (907457105386295976506192111692025343926146242781238) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel089
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
  base := (21866486356784352438204286606576185044257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2064602817691653766276409355980711975000000000000)
      constant := (51503338895950531339139428061793817347266403198866) }

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
  base := (4373296401980690391876517586924076533427/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-7434423547991560569455846726407805235000000000000)
      constant := (185503588424047366543128753467751241969917626889868) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel090
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
  base := (45696120106628902115389219279672996965729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2086717332388506257663116346130217450000000000000)
      constant := (52629436269885021236238596666176731683021209848201) }

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
  base := (45696112247694907027762141689131688778281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4174475903148701847270487211854391150000000000000)
      constant := (105310866511710948074773540984598280180836724978978) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel091
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
  base := (47691758505758503173921746960497153946669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2108831847085358749049823336279722925000000000000)
      constant := (53767695226892859752100671412576379875466350027061) }

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
  base := (47691751402256458091197158731984522744503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-37968448516718830403589536181340014525000000000000)
      constant := (968296673770635009465545740148382144311068363418126) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel092
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
  base := (1988795365920104639755394480769123955431/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-426189272356442248087306065285845680000000000000)
      constant := (10983623142737993935161179390421331620954257139195) }

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
  base := (49719877728001140207275651157607668844829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-38366613905099344181744687455990508700000000000000)
      constant := (989014566658735441431617764450501337440198641489818) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel093
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
  base := (51780493670447437020271683873709844386063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2153060876479063731823237316578733875000000000000)
      constant := (56080697682656923216582575059561419205032853324647) }

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
  base := (51780487868787549883339957838850334625471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4307197699275539773322204303404555875000000000000)
      constant := (112216830712697366474091103603894306471287692129198) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel094
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
  base := (2693679203379792989592065917228877400063/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-435035078235183244641988861345647870000000000000)
      constant := (11451088218247074683585708544729948138910690762588) }

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
  base := (53873578825261982663027054910514002684559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-39162944681860371738054990005291497050000000000000)
      constant := (1031107402272773183745345480322944010665961564348478) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel095
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
  base := (349994704083123930200124926530878396111/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-439457981174553742919330259375548965000000000000)
      constant := (11688469180277801971054827943687381230648682488288) }

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
  base := (55999147916848237419007886522810673268371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-39561110070240885516210141279941991225000000000000)
      constant := (1052482343550992681411056949024205234280991732864582) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel096
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
  base := (58157197026759919240927327948733196262043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2219404420569621205983358287027250300000000000000)
      constant := (59641412079122106936934251986876035394980697165267) }

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
  base := (1817412273368734620117597121492802981641/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4439919495402377699373921394954720600000000000000)
      constant := (119341811070922173045612113385047513840239389269056) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel097
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
  base := (30173857521077792292728152548920575746657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2241518935266473697370065277176755775000000000000)
      constant := (60852639594049483081743736755687760629362428610066) }

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
  base := (7543463897109531385718784047806389926171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-40357440847001913072520443829242979575000000000000)
      constant := (1095889269988928163411011201459233620144646209137456) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel098
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
  base := (62570704781516689247082572482925130061331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2263633449963326188756772267326261250000000000000)
      constant := (62076028419012357032391369737773159287265427324939) }

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
  base := (31285350645130529742568809046392207388507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-40755606235382426850675595103893473750000000000000)
      constant := (1117921254115078896715671471320745181616680079996588) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel099
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
  base := (1620654113262224202210991635638110541479/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-457149592932035736028695851495153345000000000000)
      constant := (12662315705947036533732246715670539410176693199608) }

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
  base := (16206540344340888375237654288707424662977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4572641291529215625425638486504885325000000000000)
      constant := (126685805731194586419016853193720838836541428904904) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel100
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
  base := (33557046378341752681451628350690411364879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2307862479357031171530186247625272200000000000000)
      constant := (64559289904519073969854366624419576858212414609102) }

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
  base := (67114089909205731194158788257645780243537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-41551937012143454406985897653194462100000000000000)
      constant := (1162642261996234742292149836120203885289436211399554) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel101
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
  base := (69434488090333701303917484431858163314099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2329976994053883662916893237774777675000000000000)
      constant := (65819162523967904392720977323831653053119741922731) }

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
  base := (34717242759555778460406594355996669743607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-41950102400523968185141048927844956275000000000000)
      constant := (1185331285013186744885235808045577210334271074424988) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel102
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
  base := (2243354665844154598439672042548327431337/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2352091508750736154303600227924283150000000000000)
      constant := (67091196370743586229102579137321810358292170110496) }

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
  base := (71787346985454297360849567152763596715293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4705363087656053551477355578055050050000000000000)
      constant := (134248813368915038619252095388468438471197787529034) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel103
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
  base := (74172675312192755639466358293102439782339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2374206023447588645690307218073788625000000000000)
      constant := (68375391429347411124056420474425224920692743455291) }

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
  base := (74172673216241614633158559409371003227863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-42746433177284995741451351477145944625000000000000)
      constant := (1231366367639050221436419998397635441435090790599246) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel104
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
  base := (9573808140930593492398670876451512470077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2396320538144441137077014208223294100000000000000)
      constant := (69671747685924667878912350116682434895055182104104) }

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
  base := (38295231617671028777228265979295454756203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-43144598565665509519606502751796438800000000000000)
      constant := (1254712426720832012805219395688623019600068778019052) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel105
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
  base := (39520358939055496938311334105311396757379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2418435052841293628463721198372799575000000000000)
      constant := (70980265128090052385235928267593171765483577274102) }

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
  base := (79040716170177667245984479542847904346783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4838084883782891477529072669605214775000000000000)
      constant := (142030833038130599682055338436025985153223813772654) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel106
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
  base := (81523432782286019618649297520026848889521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2671730000000000000000000000000000000000000000
      center := (16964385)
      previous := (0)
      next := (15096375)
      square := (394282263413027029557711419578100000000000000)
      linear := (-46048105047889549431140154500420850000000000000)
      constant := (1364168749901351905500474356885089289548359994133) }

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
  base := (81523431240726211541821200008680589071073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 48091140000000000000000000000000000000000000000
      center := (305438805)
      previous := (0)
      next := (271654875)
      square := (7097080741434486532038805552405800000000000000)
      linear := (-829074138536349756149373684926366550000000000000)
      constant := (24567199609571055378758032157873524333054944159322) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel107
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
  base := (84038609140970584061201027773384162969793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2462664082234998611237135178671810525000000000000)
      constant := (73633783526071516312874635374424933651138310775017) }

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
  base := (84038607749693332329323755318921754708073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-44339094730807050854071956575747921325000000000000)
      constant := (1326064672435375119447064560311081102132002718198066) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel108
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
  base := (43293123164636151574466563015239762765773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2484778596931851102623842168821316000000000000000)
      constant := (74978784463141066584247824874445461407566506191274) }

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
  base := (43293122536864925966828468479141518910731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-4970806679909729403580789761155379500000000000000)
      constant := (150031864063180201735911569884500644693270587494156) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel109
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
  base := (44583171894270783390371725090001209137421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2506893111628703594010549158970821475000000000000)
      constant := (76335946548069728914828995996413141864742951168298) }

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
  base := (89166342655582835465779814542737624918231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-45135425507568078410382259125048909675000000000000)
      constant := (1374727891564971700394647725516779907541544968538702) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel110
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
  base := (18355780203868624175485100626825717853589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-505801525265111217079451229824065390000000000000)
      constant := (15541053954757083140459729071133275154603137496541) }

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
  base := (45889449998540460292249433062109292693619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-45533590895948592188537410399699403850000000000000)
      constant := (1399388017297449341490587703195086352744560969417996) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel111
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
  base := (47211958787587166693381624390763455750601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2551122141022408576783963139269832425000000000000)
      constant := (79086754133965574217852577056358611558967564023138) }

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
  base := (94423916652865060072037868359463788601191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5103528476036567329632506852705544225000000000000)
      constant := (158251905961393363352659513523824786198977526322558) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel112
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
  base := (97101393056850666203514395993728329332047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2573236655719261068170670129419337900000000000000)
      constant := (80480399622957683939733620470163526683429442635943) }

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
  base := (48550696112392657310565334688665503094413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-46329921672709619744847712949000392200000000000000)
      constant := (1449365300528762818741940111582239353498328797288692) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel113
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
  base := (49905663553743679370634740414279812697181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2595351170416113559557377119568843375000000000000)
      constant := (81886206235708196344513678484460542161223357567178) }

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
  base := (24952831589223201687162792915010014529833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-46728087061090133523002864223650886375000000000000)
      constant := (1474682457835391654505216689393614724493593389167944) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel114
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
  base := (102553719408013903277161421219455913665519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2617465685112966050944084109718348850000000000000)
      constant := (83304173967699019119921148052650229956803158512711) }

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
  base := (102553718730963511774299396742663762232547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5236250272163405255684223944255708950000000000000)
      constant := (166690958387924096668418602129430450919902365640886) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel115
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
  base := (105328569673164655271338347042750733689569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2639580199809818542330791099867854325000000000000)
      constant := (84734302814890742529377799458815422090480790577161) }

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
  base := (164575889160152056769473870696679826133/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-9504883567570232215862633354590374945000000000000)
      constant := (305194760684804842185924047794093102717161947483008) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel116
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
  base := (108135877647894961043313182951222006331983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2661694714506671033717498090017359800000000000000)
      constant := (86176592773671891174221463713723720241179949385127) }

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
  base := (54067938548570903128077098397132489123109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-47922583226231674857468318047602368900000000000000)
      constant := (1551947991568683560183849194289253815371959868835156) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel117
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
  base := (110975643104177578374351596718976139746061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2683809229203523525104205080166865275000000000000)
      constant := (87631043840813560768030927706954324972334340844309) }

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
  base := (110975642607495631729498861582727159243741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5368972068290243181735941035805873675000000000000)
      constant := (175349021096370463331386484456625969112343819504458) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel118
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
  base := (56923932919069491127768830252677165570457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2705923743900376016490912070316370750000000000000)
      constant := (89097656013428867742054215393491702565087305054466) }

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
  base := (1423098317378138846864798034646891288393/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-9743782800598540482755724119380671450000000000000)
      constant := (320910679653631271821977085921908062229487514104096) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel119
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
  base := (116752545667499450047734005501318023729049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2728038258597228507877619060465876225000000000000)
      constant := (90576429288936700418448015616784538327811844049281) }

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
  base := (23350509052728000809129135856354141243349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 509766084000000000000000000000000000000000000000
      center := (3237651333)
      previous := (0)
      next := (2879541675)
      square := (75229055859205557239611338855501480000000000000)
      linear := (-9823415878274643238386754374310770285000000000000)
      constant := (326236923344964097619201517563393003469558705387658) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel120
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
  base := (5984484121464233149743471140821624587921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28320338000000000000000000000000000000000000000
      center := (179822481)
      previous := (0)
      next := (160021575)
      square := (4179391992178086513311741047527860000000000000)
      linear := (-550030554658816199852865210123076340000000000000)
      constant := (18413472733005862980193298056581994812078066874596) }

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
  base := (119689682065150315875911042310611674107173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5501693864417081107787658127356038400000000000000)
      constant := (184226093910656111423381929395771510347460987584474) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel121
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
  base := (61329637988889996800239702644626063975767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2772267287990933490651033040764887175000000000000)
      constant := (93570459139643367438487655067960229679465845249246) }

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
  base := (122659275649485234732046669826282136084229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-49913410168134243748244074420854839775000000000000)
      constant := (1685104083644376210707781248884778798196187505744618) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel122
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
  base := (125661326182701714786991271969395455431779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2794381802687785982037740030914392650000000000000)
      constant := (95085715710934018437643204699894822857995958610651) }

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
  base := (125661325886738599919171395461721998575201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-50311575556514757526399225695505333950000000000000)
      constant := (1712392332037123234375587095273326267308291896641442) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel123
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
  base := (64347916463781053108954168136200698378331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2816496317384638473424447021063898125000000000000)
      constant := (96613133377251782092043609228737751965472885795878) }

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
  base := (64347916330381923658732550101602621666143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5634415660543919033839375218906203125000000000000)
      constant := (193322176704949142692571899922285052575323835832668) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel124
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
  base := (131762796108207880662237758980647646644881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2838610832081490964811154011213403600000000000000)
      constant := (98152712137121830252592468013377657380943797944889) }

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
  base := (131762795867715915406620158646509575185639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-51107906333275785082709528244806322300000000000000)
      constant := (1767625858540165015103488108627671757567943383033838) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel125
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
  base := (134862215631513540041533902452176436619077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2860725346778343456197861001362909075000000000000)
      constant := (99704451989225490128289815567491655611906418944013) }

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
  base := (67431107707373875995239122483714641004711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-51506071721656298860864679519456816475000000000000)
      constant := (1795571136600326287882120508454944411337968602021724) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel126
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
  base := (137994091414213224690091797568496247177831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2882839861475195947584567991512414550000000000000)
      constant := (101268352932383703074338986024222125717153860013439) }

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
  base := (137994091218845015852546714152167155056299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5767137456670756959891092310456367850000000000000)
      constant := (202637269389318572750017630316737852216817796709062) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel127
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
  base := (141158423381856365252782299762354856883847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2904954376172048438971274981661920025000000000000)
      constant := (102844414965542236446525129679671344375508586890143) }

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
  base := (70579211602892155323918267761383018907209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-52302402498417326417174982068757804825000000000000)
      constant := (1852118722231869330659620116218931491010707141299556) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel128
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
  base := (72177605733937003374201259109804153617103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2927068890868900930357981971811425500000000000000)
      constant := (104432638087758462592161021776622485544240279540814) }

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
  base := (144355211309201845874346881587870136626733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2548830420000000000000000000000000000000000000000
      center := (16188256665)
      previous := (0)
      next := (14397708375)
      square := (376145279296027786198056694277507400000000000000)
      linear := (-52700567886797840195330133343408299000000000000000)
      constant := (1880721029767417810808704160562302881124377325561786) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell139.Kernel129
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
  base := (147584455612744068464093801736556577864691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (899112405)
      previous := (0)
      next := (800107875)
      square := (20896959960890432566558705237639300000000000000)
      linear := (-2949183405565753421744688961960930975000000000000)
      constant := (106033022298189538789120943340919103509688183692779) }

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
  base := (147584455469760811571167094833620819204251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 283203380000000000000000000000000000000000000000
      center := (1798695185)
      previous := (0)
      next := (1599745375)
      square := (41793919921780865133117410475278600000000000000)
      linear := (-5899859252797594885942809402006532575000000000000)
      constant := (212171371899487627619110888489266932770732529356838) }

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
end ForestUnimodality.Stage99KernelData.Cell139.Kernel129
