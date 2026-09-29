import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell075.Parameters
import ForestUnimodality.BinomialMassData.Q51_101.Batch000_049
import ForestUnimodality.BinomialMassData.Q51_101.Batch050_099
import ForestUnimodality.BinomialMassData.Q51_101.Batch100_149
import ForestUnimodality.BinomialMassData.Q51_101.Batch150_199
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch000_049
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch050_099
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch100_149
import ForestUnimodality.BinomialMassData.Q10429_20604.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree000.table
  base := (839350368477915708587033803/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (164857212375408845872470920000000000000)
      linear := (-2424331854343381197677137475000000000)
      constant := (209837592119478927146758450750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree000.table
  base := (839350368477915708587033803/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (164857212375408845872470920000000000000)
      linear := (-2424331854343381197677137475000000000)
      constant := (209837592119478927146758450750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree001.table
  base := (57812657156324434266818278363016740380143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-1723089611137618761775699897222475000000000)
      constant := (1179935112646101269076290046960321262235677486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree001.table
  base := (461597809680861195151371003257038698812839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-17969483289323072145768836616148629900000000000)
      constant := (12252095695021087754977602704706416192924993432039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12499050137222322353/25000000000000000000)
  directionHi := (49996200548889289413/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree002.table
  base := (26909681246310584577947767544936740371309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-6842897226058161383907790630124950000000000)
      constant := (1376008591776705764689337198273393342638615545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree002.table
  base := (67043124619552983632686359000249402991289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-8920417330012282153899309157200497475000000000)
      constant := (1783389635386005185772409271315978098949175770489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499050137222322353/25000000000000000000)
  centralHi := (49996200548889289413/100000000000000000000)
  directionLo := (35352652441682206003/50000000000000000000)
  directionHi := (70705304883364412007/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree003.table
  base := (5236023637825122727011436949858059440271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-5119807614920542622132090732902475000000000)
      constant := (431198022720273729448625723175697689801635768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree003.table
  base := (2085354462271852704992934809971670620067/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-1483162648632644030150712128929315275000000000)
      constant := (124087722445315987130550744826070650001604039260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35352652441682206003/50000000000000000000)
  centralHi := (70705304883364412007/100000000000000000000)
  directionLo := (43297979768039619967/50000000000000000000)
  directionHi := (17319191907215847987/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree004.table
  base := (7021302758464684584377758128612389703019/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-6818166616812004552310286150742475000000000)
      constant := (293407886440134895336975732227154849441987276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree004.table
  base := (6988726139996100109836948747230388730559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-17776510345375310388813509163527177475000000000)
      constant := (759782690841441321693815693282550159387258263036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43297979768039619967/50000000000000000000)
  centralHi := (17319191907215847987/20000000000000000000)
  directionLo := (12499050137222322353/12500000000000000000)
  directionHi := (3999696043911143153/4000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree005.table
  base := (3231553515494372299864537982438758586841/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-34066102474813865929953926274329900000000000)
      constant := (867256050895430591715368183966118908609126025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree005.table
  base := (40210291314799379846671856629807206332873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-44409113706113649012541218333381034950000000000)
      constant := (1123250170929772376666022649337315944058559067273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499050137222322353/12500000000000000000)
  centralHi := (3999696043911143153/4000000000000000000)
  directionLo := (55897451522014374433/50000000000000000000)
  directionHi := (111794903044028748867/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree006.table
  base := (61542448493098079209703539145186963026731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-40859538482379713650666707945689900000000000)
      constant := (689840502431189982943826189523741609835682931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree006.table
  base := (30638561689394396354825642299984297860361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-5918356302386297471939490926634190550000000000)
      constant := (99333886519110036316770283985782141369853800129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897451522014374433/50000000000000000000)
  centralHi := (111794903044028748867/100000000000000000000)
  directionLo := (122465180422635013171/100000000000000000000)
  directionHi := (30616295105658753293/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree007.table
  base := (48893351957671330071612451703123195131873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-47652974489945561371379489617049900000000000)
      constant := (583154287295027403234299383139624013540236473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree007.table
  base := (48694017473719683764393280449571935505361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-124242599473679410964739236692068789900000000000)
      constant := (1512549390943615275526833915824049596123577846161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122465180422635013171/100000000000000000000)
  centralHi := (30616295105658753293/25000000000000000000)
  directionLo := (33069378287618010293/25000000000000000000)
  directionHi := (132277513150472041173/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree008.table
  base := (9984722888950016564730279124031228970481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-13611602624377852273023067822102475000000000)
      constant := (129396851058092959148522456052192366727876681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree008.table
  base := (39781417546810109481523544964040446133421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-141954785504405467434567636704722149900000000000)
      constant := (1343442897534039514353670891080517777409278842221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33069378287618010293/25000000000000000000)
  centralHi := (132277513150472041173/100000000000000000000)
  directionLo := (141410609766728824013/100000000000000000000)
  directionHi := (70705304883364412007/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree009.table
  base := (6635532517768884073994221553038083905533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-61239846505077256812805052959769900000000000)
      constant := (477824023912397995658879911563601569601710665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree009.table
  base := (33047299379274249877900601591782999933209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-17740774615014613767155115190819501100000000000)
      constant := (137900321714558749660873320591549940515094187601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141410609766728824013/100000000000000000000)
  centralHi := (70705304883364412007/50000000000000000000)
  directionLo := (37497150411666967059/25000000000000000000)
  directionHi := (149988601646667868237/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree010.table
  base := (5562448814655443526872571420337696029529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-68033282512643104533517834631129900000000000)
      constant := (455729654882145170595823647867673185986126645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree010.table
  base := (27700322908953459032550541779170265386381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-177379157565857580374224436730028869900000000000)
      constant := (1184532916241999990658738456708699776864035183181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37497150411666967059/25000000000000000000)
  centralHi := (149988601646667868237/100000000000000000000)
  directionLo := (39525467022262666143/25000000000000000000)
  directionHi := (158101868089050664573/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree011.table
  base := (1170108697757315041746478781854101661511/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-18706679630052238063557654075622475000000000)
      constant := (111702785932311851408150654968259430245368555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree011.table
  base := (23303699025263654743047149757515220123587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-195091343596583636844052836742682229900000000000)
      constant := (1162143721416858798641690105061133918285329277187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525467022262666143/25000000000000000000)
  centralHi := (158101868089050664573/100000000000000000000)
  directionLo := (165818638164026466361/100000000000000000000)
  directionHi := (82909319082013233181/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree012.table
  base := (4922686443821294682836456872834271252083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-20405038631943699993735849493462475000000000)
      constant := (112112456965936830906664264041867101042498683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree012.table
  base := (9801416562839029143077834949885349962937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-11822418312628316295215624264185310550000000000)
      constant := (64843344612838225214560721280287736836884977393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165818638164026466361/100000000000000000000)
  centralHi := (82909319082013233181/50000000000000000000)
  directionLo := (173191919072158479869/100000000000000000000)
  directionHi := (17319191907215847987/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree013.table
  base := (16518135919774906684496067170059590812107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-88413590535340647695656179645209900000000000)
      constant := (459015346600057770314369277162651585874303507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree013.table
  base := (16439069079725624715038125914215509555923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-230515715658035749783709636767988949900000000000)
      constant := (1195432769547469484483439486469879390485903330323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173191919072158479869/100000000000000000000)
  centralHi := (17319191907215847987/10000000000000000000)
  directionLo := (7210554586296047161/4000000000000000000)
  directionHi := (90131932328700589513/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree014.table
  base := (6888735652518259671005917850232117161289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-47603513271453247708184480658284950000000000)
      constant := (238708743806294860068114316438602127162309089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree014.table
  base := (3426539342035283259035562575732461017051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-62056975422190451563384509195160577475000000000)
      constant := (311020580903748328915696254678540050493171789851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7210554586296047161/4000000000000000000)
  centralHi := (90131932328700589513/50000000000000000000)
  directionLo := (187068653094382992551/100000000000000000000)
  directionHi := (23383581636797874069/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree015.table
  base := (1139231027320361850920066041481825669397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-51000231275236171568540871493964950000000000)
      constant := (251438234774724022554088604813792268267593985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree015.table
  base := (1415997408544665012837673779234053297151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-7387224658874662853426845466480435275000000000)
      constant := (36419700619872448478120449631927335245239188878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187068653094382992551/100000000000000000000)
  centralHi := (23383581636797874069/12500000000000000000)
  directionLo := (193634452099494332879/100000000000000000000)
  directionHi := (2420430651243679161/1250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree016.table
  base := (1860969655933935700349233676019502987637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-108793898558038190857794524659289900000000000)
      constant := (534802628251101576724503687124013149884425185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree016.table
  base := (2311723414342366103143673180830108141711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-70913068437553479798298709201487257475000000000)
      constant := (348746021300653293863842166097044266232497762511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193634452099494332879/100000000000000000000)
  centralHi := (2420430651243679161/1250000000000000000)
  directionLo := (12499050137222322353/6250000000000000000)
  directionHi := (199984802195557157649/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree017.table
  base := (7469534456248785752573110765618809104247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-115587334565604038578507306330649900000000000)
      constant := (572731299311185810687473452044690771672423647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree017.table
  base := (3708716195306269304933814595490049395449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 459045000000000000000000000000000000000000000
      center := (7711956)
      previous := (3855978)
      next := (3855978)
      square := (30270751621947821461411365388560000000000000)
      linear := (-521391798928961895610766845706924550000000000)
      constant := (2585641029489663155706534165779917357446777241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499050137222322353/6250000000000000000)
  centralHi := (199984802195557157649/100000000000000000000)
  directionLo := (206139615742634197397/100000000000000000000)
  directionHi := (103069807871317098699/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree018.table
  base := (731181392969192781606163284747494169763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-30595192643292471574805022000502475000000000)
      constant := (154071471422082524977247355753905426051504726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree018.table
  base := (14506805713926199419564501558658755841/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-8863240161435167559245878800868215275000000000)
      constant := (44685560084130809830619677559733652297353784900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206139615742634197397/100000000000000000000)
  centralHi := (103069807871317098699/50000000000000000000)
  directionLo := (10605795732504661801/5000000000000000000)
  directionHi := (212115914650093236021/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree019.table
  base := (2207065928809647035499784715657507969051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-64587103290367867009966434836684950000000000)
      constant := (332577799386745204816526566447743788792289251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree019.table
  base := (437232502405027089357626713173125920237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-168394415921196044301340018421954554950000000000)
      constant := (868357707657137362852823732508095379185450969185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10605795732504661801/5000000000000000000)
  centralHi := (212115914650093236021/100000000000000000000)
  directionLo := (217928385753601166791/100000000000000000000)
  directionHi := (27241048219200145849/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree020.table
  base := (3138150824204696155664538950524104223693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-135967642588301581740645651344729900000000000)
      constant := (719081070249751378990747737316994387185892293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree020.table
  base := (3100837403441899858555509078013990070997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-354501017873118145072508436856562469900000000000)
      constant := (1877932253782107886993631684009603034269739272597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217928385753601166791/100000000000000000000)
  centralHi := (27241048219200145849/12500000000000000000)
  directionLo := (223589806088057497733/100000000000000000000)
  directionHi := (111794903044028748867/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree021.table
  base := (400028945092867239757680603060206278979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-142761078595867429461358433016089900000000000)
      constant := (777844372909731757027595899901198721259323895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree021.table
  base := (983458927373120294726400220388292758951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-20678511327991344530129824270511990550000000000)
      constant := (112875801490495947582733119135318640973943094639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223589806088057497733/100000000000000000000)
  centralHi := (111794903044028748867/50000000000000000000)
  directionLo := (229111373475477885019/100000000000000000000)
  directionHi := (11455568673773894251/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree022.table
  base := (982090930161013131385955775499470621989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-149554514603433277182071214687449900000000000)
      constant := (841261657892180855638879535770757899814909789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree022.table
  base := (952566426792806855732858971793666375099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-389925389934570258012165236881869189900000000000)
      constant := (2197734345332316005964308078923591679540893122299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229111373475477885019/100000000000000000000)
  centralHi := (11455568673773894251/5000000000000000000)
  directionLo := (29312870873225390269/12500000000000000000)
  directionHi := (234502966985803122153/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree023.table
  base := (34374362625658789420809528101827054129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-78173975305499562451391998179404950000000000)
      constant := (454588727341671427897072565981678087779169929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree023.table
  base := (42566325072065015121836216289933628693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-407637575965296314481993636894522549900000000000)
      constant := (2375438265111695386685710278918460951848319259093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29312870873225390269/12500000000000000000)
  centralHi := (234502966985803122153/100000000000000000000)
  directionLo := (239773354638227945717/100000000000000000000)
  directionHi := (119886677319113972859/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree024.table
  base := (-752788216879257672935964201287639446307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-163141386618564972623496778030169900000000000)
      constant := (981460105835222169402446755123182390008222293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree024.table
  base := (-387981967410610949903545386463115276207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-23630542333112353941767890939287550550000000000)
      constant := (142474133572486469046601298283348591648482181577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239773354638227945717/100000000000000000000)
  centralHi := (119886677319113972859/50000000000000000000)
  directionLo := (244930360845270026343/100000000000000000000)
  directionHi := (30616295105658753293/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree025.table
  base := (-1493458400929029239420646479545937098387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-169934822626130820344209559701529900000000000)
      constant := (1057998027661391268669335636075524395659354213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree025.table
  base := (-378484402437631470405209427505747898777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-110765487006687106855412609229957317475000000000)
      constant := (691183300909719696968948973910308989801831715623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244930360845270026343/100000000000000000000)
  centralHi := (30616295105658753293/12500000000000000000)
  directionLo := (12499050137222322353/5000000000000000000)
  directionHi := (249981002744446447061/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree026.table
  base := (-1081268507060719460652083766527687114207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-88364129316848334032461170686444950000000000)
      constant := (569348301988491911892977668792444763747974393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree026.table
  base := (-2180604764151192432642405902060584140441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-460774134057474483891478836932482629900000000000)
      constant := (2975789232995162222217246627138375779707922894759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499050137222322353/5000000000000000000)
  centralHi := (249981002744446447061/100000000000000000000)
  directionLo := (254931602204284786433/100000000000000000000)
  directionHi := (127465801102142393217/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree027.table
  base := (-553578213825348725914745918560107518093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-183521694641262515785635123044249900000000000)
      constant := (1223475583385750544003325409693004016039666535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree027.table
  base := (-1391903934511491836898250163742966687751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-26582573338233363353405957608063110550000000000)
      constant := (177638578313956765914519023911936253117974842161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254931602204284786433/100000000000000000000)
  centralHi := (127465801102142393217/50000000000000000000)
  directionLo := (64946969652059429951/25000000000000000000)
  directionHi := (51957575721647543961/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree028.table
  base := (-829048573553223453358181408637753547299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-47578782662207090876586976178902475000000000)
      constant := (328066721796407516697280510163510576064002901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree028.table
  base := (-3330197048115642580151978739458546670303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-496198506118926596831135636957789349900000000000)
      constant := (3429672287196980176449433341408777958147637891297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64946969652059429951/25000000000000000000)
  centralHi := (51957575721647543961/20000000000000000000)
  directionLo := (33069378287618010293/12500000000000000000)
  directionHi := (52911005260188816469/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree029.table
  base := (-1906554338477837182228782434680234408089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-98554283328197105613530343193484950000000000)
      constant := (702506378720680905232187140053022978803084111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree029.table
  base := (-3825411878026093893077408815899788785879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-513910692149652653300964036970442709900000000000)
      constant := (3672173231868866930806810686266832320927240882921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33069378287618010293/12500000000000000000)
  centralHi := (52911005260188816469/20000000000000000000)
  directionLo := (134618889843158687401/50000000000000000000)
  directionHi := (269237779686317374803/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree030.table
  base := (-4263438113624022617059884487113631830583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-203902002663960058947773468058329900000000000)
      constant := (1501664189607106345280749017075000841696222817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree030.table
  base := (-4274235206051947131149479856239567210859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-59069208686708745530088048553677341100000000000)
      constant := (436096704592369020933485929396490277290905901549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134618889843158687401/50000000000000000000)
  centralHi := (269237779686317374803/100000000000000000000)
  directionLo := (17115029268861769641/6250000000000000000)
  directionHi := (273840468301788314257/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree031.table
  base := (-4671258588281901952805868451476712308209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-210695438671525906668486249729689900000000000)
      constant := (1602179604569427180782889608947547957743959991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree031.table
  base := (-468072342517841396460548239867123646631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-274667532105552383120310418497874714950000000000)
      constant := (2093827994058244266021918861842225653595226782845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17115029268861769641/6250000000000000000)
  centralHi := (273840468301788314257/100000000000000000000)
  directionLo := (1113468254772034267/400000000000000000)
  directionHi := (278367063693008566751/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree032.table
  base := (-5040028535310574469563086061438255487711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-217488874679091754389199031401049900000000000)
      constant := (1706523722839201062310448981304705155769860089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree032.table
  base := (-5048316875188845502190730013112514922827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-567047250241830822710449237008402789900000000000)
      constant := (4460438890373524923652734998981722347743100851573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1113468254772034267/400000000000000000)
  centralHi := (278367063693008566751/100000000000000000000)
  directionLo := (282821219533457648027/100000000000000000000)
  directionHi := (70705304883364412007/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree033.table
  base := (-5372682435951890369471421499556091775077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-224282310686657602109911813072409900000000000)
      constant := (1814666609773279875951398175600200007802439523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree033.table
  base := (-5379933434178998813949237076324573340653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-64973270696950764353364181891228461100000000000)
      constant := (527015736513730375771582699528942494329727637883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282821219533457648027/100000000000000000000)
  centralHi := (70705304883364412007/25000000000000000000)
  directionLo := (11488252245678939901/4000000000000000000)
  directionHi := (143603153070986748763/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree034.table
  base := (-5671710212772016157229393026432867858713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-231075746694223449830624594743769900000000000)
      constant := (1926582865671566157191307607057624914973268687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree034.table
  base := (-5678047875937065359684752981074223549027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (15423912)
      previous := (7711956)
      next := (7711956)
      square := (60541503243895642922822730777120000000000000)
      linear := (-2084676893782985936505557221569929100000000000)
      constant := (17424562422789591026870218796984702260187380157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11488252245678939901/4000000000000000000)
  centralHi := (143603153070986748763/50000000000000000000)
  directionLo := (291525440325611653559/100000000000000000000)
  directionHi := (7288136008140291339/2500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree035.table
  base := (-2969612292689022694184234836057463138431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-118934591350894648775668688207564950000000000)
      constant := (1021125469340673972335100380050738568524865369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree035.table
  base := (-5944759165954611272378082491809621078797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-620183808334008992119934437046362869900000000000)
      constant := (5338053933627686606731762579051057074905873879603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291525440325611653559/100000000000000000000)
  centralHi := (7288136008140291339/2500000000000000000)
  directionLo := (147890755649538925919/50000000000000000000)
  directionHi := (295781511299077851839/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree036.table
  base := (-1544254554244721024397728266510704362773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-61165654677338786318012539521622475000000000)
      constant := (540413135461307796982019965962458404795352627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree036.table
  base := (-3090923766581944295716171942190012685773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-35438666353596391588320157614389790550000000000)
      constant := (313897809693781327555540291107519183741212162203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147890755649538925919/50000000000000000000)
  centralHi := (295781511299077851839/100000000000000000000)
  directionLo := (37497150411666967059/12500000000000000000)
  directionHi := (299977203293335736473/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree037.table
  base := (-6386612201241862998829955846293960239371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-251456054716920992992762939757849900000000000)
      constant := (2284772158486715446352112012161666611598176429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree037.table
  base := (-6390822872702820645443489680190639942879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-655608180395461105059591237071669589900000000000)
      constant := (5971978401020098287338487197325551145257940125921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37497150411666967059/12500000000000000000)
  centralHi := (299977203293335736473/100000000000000000000)
  directionLo := (304115015356059054133/100000000000000000000)
  directionHi := (152057507678029527067/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree038.table
  base := (-262771888108051477228010759352437572271/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-258249490724486840713475721429209900000000000)
      constant := (2411596622536886276283588946462390808131588225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree038.table
  base := (-3286482898719904259285777873151828791557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-336660183213093580764709818542161474950000000000)
      constant := (3151736717488697227796922983704025486362547638843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304115015356059054133/100000000000000000000)
  centralHi := (152057507678029527067/50000000000000000000)
  directionLo := (308197278758818362133/100000000000000000000)
  directionHi := (154098639379409181067/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree039.table
  base := (-1681542091076602803565211405980918038219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-66260731683013172108547125775142475000000000)
      constant := (635528690610629581048096969419123930092127981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree039.table
  base := (-1345872491040925211569239415099664737353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-76781394717434801999916448566330701100000000000)
      constant := (738290761979525381045284363684530737195608657915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308197278758818362133/100000000000000000000)
  centralHi := (154098639379409181067/50000000000000000000)
  directionLo := (3122261723553385101/1000000000000000000)
  directionHi := (312226172355338510101/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree040.table
  base := (-685815492664388337942031245572741116253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-135918181369809268077450642385964950000000000)
      constant := (1338158549510193599312955452474260339365515735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree040.table
  base := (-6860934058724765454012288780913856387487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-708744738487639274469076437109629669900000000000)
      constant := (6995384227181122991253539301436952771328228538913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3122261723553385101/1000000000000000000)
  centralHi := (312226172355338510101/100000000000000000000)
  directionLo := (39525467022262666143/12500000000000000000)
  directionHi := (63240747235620265829/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree041.table
  base := (-3483022680054448172153206103054174444427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-139314899373592191937807033221644950000000000)
      constant := (1407097794541995768313168462360749816492400173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree041.table
  base := (-3484230965649280933577554721557998320573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-363228462259182665469452418561141514950000000000)
      constant := (3677877406188993375348970106314433055114402385027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525467022262666143/12500000000000000000)
  centralHi := (63240747235620265829/20000000000000000000)
  directionLo := (320131883514146502201/100000000000000000000)
  directionHi := (160065941757073251101/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree042.table
  base := (-3525254344915344183606241928779352890383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-142711617377375115798163424057324950000000000)
      constant := (1477871703953993989360407793017514721165203017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree042.table
  base := (-7052608749214878446502266859076761525023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-82685456727676820823192581903881821100000000000)
      constant := (858412336749802209254008065039267746642456468953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320131883514146502201/100000000000000000000)
  centralHi := (160065941757073251101/50000000000000000000)
  directionLo := (81003102915737054623/25000000000000000000)
  directionHi := (324012411662948218493/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree043.table
  base := (-7112112590134671738536715947259263234873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-292216670762316079317039629786009900000000000)
      constant := (3100954764646582994134994967621328955741060527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree043.table
  base := (-3556968279239161610260529676489906670527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-380940648289908721939280818573794874950000000000)
      constant := (4052618984818514639557805629083692500339834543873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81003102915737054623/25000000000000000000)
  centralHi := (324012411662948218493/100000000000000000000)
  directionLo := (163923505774007728491/50000000000000000000)
  directionHi := (327847011548015456983/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree044.table
  base := (-7151338737928580295844190705367152829843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-299010106769881927037752411457369900000000000)
      constant := (3249824745713640789991873665650565273982771557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree044.table
  base := (-1430584411135528601146992749454969434049/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-779593482610543500348390037160243109900000000000)
      constant := (8494322980948688340064355308712621860826476293755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163923505774007728491/50000000000000000000)
  centralHi := (327847011548015456983/100000000000000000000)
  directionLo := (165818638164026466361/50000000000000000000)
  directionHi := (331637276328052932723/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree045.table
  base := (-1433719168050989055980948033908371817047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-305803542777447774758465193128729900000000000)
      constant := (3402349181888620505104358623506573995471517765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree045.table
  base := (-7169969548444092842536378818789907144321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-88589518737918839646468715241432941100000000000)
      constant := (988106148585474910529480695370099821561805847431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165818638164026466361/50000000000000000000)
  centralHi := (331637276328052932723/100000000000000000000)
  directionLo := (1676923545660431233/500000000000000000)
  directionHi := (335384709132086246601/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree046.table
  base := (-7164230688344280737288711055631243736453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-312596978785013622479177974800089900000000000)
      constant := (3558524535554179665683385734340991082644442947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree046.table
  base := (-3582710973928414194419852559894879853019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-407508927335997806644023418592774914950000000000)
      constant := (4650562970103681455449528621067341726515937623781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1676923545660431233/500000000000000000)
  centralHi := (335384709132086246601/100000000000000000000)
  directionLo := (33909073002507581593/10000000000000000000)
  directionHi := (339090730025075815931/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree047.table
  base := (-892317192140951349081473720230313408731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-79847603698144867549972689117862475000000000)
      constant := (929586951253941723658335585301426220835070138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree047.table
  base := (-7139570091645118647896618629937777401789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-832730040702721669757875237198203189900000000000)
      constant := (9718827073023360502126803188439088726991035419011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33909073002507581593/10000000000000000000)
  centralHi := (339090730025075815931/100000000000000000000)
  directionLo := (85689170573891516087/25000000000000000000)
  directionHi := (342756682295566064349/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree048.table
  base := (-3545883031939044264144218482517929583449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-163091925400072658960301769071404950000000000)
      constant := (1940908221657759378680871325368032200319236751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree048.table
  base := (-709266065165609466588397616838662996451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-47246790374080429234872424289492030550000000000)
      constant := (563669566156790818776635096914224635627278839305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85689170573891516087/25000000000000000000)
  centralHi := (342756682295566064349/100000000000000000000)
  directionLo := (346383838144316959739/100000000000000000000)
  directionHi := (17319191907215847987/5000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree049.table
  base := (-7024128121223751235824237102555742634623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-332977286807711165641316319814169900000000000)
      constant := (4048928289344776645456714076086718969384210777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree049.table
  base := (-439056427535455182069827992054316875401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-217038603191043445674383009305877477475000000000)
      constant := (2645698935651411532861957533449910469922423887196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346383838144316959739/100000000000000000000)
  centralHi := (17319191907215847987/5000000000000000000)
  directionLo := (69994680768445005177/20000000000000000000)
  directionHi := (174986701921112512943/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree050.table
  base := (-866975433395906142893099712840115222451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-84942680703819253340507275371382475000000000)
      constant := (1054920377348038880985898883715322219231554698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree050.table
  base := (-6936474100178544218674984566725213975827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-885866598794899839167360437236163269900000000000)
      constant := (11029053020345629893326362154105814577146963398573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69994680768445005177/20000000000000000000)
  centralHi := (174986701921112512943/50000000000000000000)
  directionLo := (176763262208411030017/50000000000000000000)
  directionHi := (70705304883364412007/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree051.table
  base := (-3413472313540827041728468152307707448713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-173282079411421430541370941578444950000000000)
      constant := (2197037273773162343525922140671789026315678687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree051.table
  base := (-3413762462965289397867394987496186274597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-173698343872669337877198930651444950000000000)
      constant := (2207770094382277300568652223775718541312836003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176763262208411030017/50000000000000000000)
  centralHi := (70705304883364412007/20000000000000000000)
  directionLo := (1785221439594838063/500000000000000000)
  directionHi := (357044287918967612601/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree052.table
  base := (-3348840509587936696971046192881226271669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-176678797415204354401727332414124950000000000)
      constant := (2286053041806067535517436225711686010802704531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree052.table
  base := (-669818295881405943073696698892694126081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-460645485428175976053508618630734994950000000000)
      constant := (5975046693912785520122197110366315560644119585595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1785221439594838063/500000000000000000)
  centralHi := (357044287918967612601/100000000000000000000)
  directionLo := (7210554586296047161/2000000000000000000)
  directionHi := (360527729314802358051/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree053.table
  base := (-511572066797174529412896566811556217/781250000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-90037757709493639131041861624902475000000000)
      constant := (1188443749350481266891638274294624433097225600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree053.table
  base := (-6548556455916260933330302295800938558149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-939003156887078008576845637274123349900000000000)
      constant := (12424870218528769959228434074995006686948405654651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7210554586296047161/2000000000000000000)
  centralHi := (360527729314802358051/100000000000000000000)
  directionLo := (181988917021210495777/50000000000000000000)
  directionHi := (72795566808484198311/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree054.table
  base := (-3189181054844866888444259659229938436011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-183472233422770202122440114085484950000000000)
      constant := (2469540169218126366700876784760077698014251789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree054.table
  base := (-51029897871674183664652817373021035589/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-106301704768644896116297115254086301100000000000)
      constant := (1434349787436820844155718735415711501676432572375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181988917021210495777/50000000000000000000)
  centralHi := (72795566808484198311/20000000000000000000)
  directionLo := (73479108253581007903/20000000000000000000)
  directionHi := (91848885316976259879/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree055.table
  base := (-1547119760550043134504212399899980261183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-93434475713276562991398252460582475000000000)
      constant := (1282005325058649946140878461073975176355672217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree055.table
  base := (-6188803165856256477381720682465239243837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-974427528948530121516502437299430069900000000000)
      constant := (13402924926846915764402084826817057859100882402563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73479108253581007903/20000000000000000000)
  centralHi := (91848885316976259879/25000000000000000000)
  directionLo := (370781746871204101637/100000000000000000000)
  directionHi := (185390873435602050819/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree056.table
  base := (-1494635083456252329146291186898273166757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-95132834715168024921576447878422475000000000)
      constant := (1330149299625182092203570802087059315425911843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree056.table
  base := (-1494705074540053515720129802919177307041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-248034928744814044496582709328020857475000000000)
      constant := (3476549746468826726761052171364904021778565248159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370781746871204101637/100000000000000000000)
  centralHi := (185390873435602050819/50000000000000000000)
  directionLo := (374137306188765985103/100000000000000000000)
  directionHi := (23383581636797874069/6250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree057.table
  base := (-1437150725675811602969749405356492461237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-96831193717059486851754643296262475000000000)
      constant := (1379201863153175630924762485245660745402921363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree057.table
  base := (-57488446469730224786120890876174231091/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-28051441694721728734893312147909355275000000000)
      constant := (400526910493124364817255547006611087387179122525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374137306188765985103/100000000000000000000)
  centralHi := (23383581636797874069/6250000000000000000)
  directionLo := (1474464986471510603/390625000000000000)
  directionHi := (377463036536706714369/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree058.table
  base := (-5498715043468858472015328902853465908031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-394118210875803795127731354856409900000000000)
      constant := (5716651569916961073832372722264535994272175769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree058.table
  base := (-2749461860570410598728029242761545624299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-513782043520354145462993818668695074950000000000)
      constant := (7470616520967833042640448887912342402223053868501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1474464986471510603/390625000000000000)
  centralHi := (377463036536706714369/100000000000000000000)
  directionLo := (380759719535609419833/100000000000000000000)
  directionHi := (190379859767804709917/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree059.table
  base := (-1307229433414331069631831140376511996097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-100227911720842410712111034131942475000000000)
      constant := (1480032283100416150040957931534428976127814503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree059.table
  base := (-2614548907073804511393699988146492168831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-522638136535717173697908018675021754950000000000)
      constant := (7736495354662940612844558330307772161173848674369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380759719535609419833/100000000000000000000)
  centralHi := (190379859767804709917/50000000000000000000)
  directionLo := (48003512906960892437/12500000000000000000)
  directionHi := (384028103255687139497/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree060.table
  base := (-493924574220562361983107520908288631491/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-203852541445467745284578459099564950000000000)
      constant := (3063619892694443485935897206136119738350801545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree060.table
  base := (-4939401099830507050869292376036961809073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-118109828789128933762849381929188541100000000000)
      constant := (1779360097021722534909533731050591022797251788503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48003512906960892437/12500000000000000000)
  centralHi := (384028103255687139497/100000000000000000000)
  directionLo := (387268904198988665759/100000000000000000000)
  directionHi := (2420430651243679161/625000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree061.table
  base := (-1157432142506508940867433808239110779693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-103624629724625334572467424967622475000000000)
      constant := (1584495806984955507037013265690630055936351707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree061.table
  base := (-4629862561706641227656758720200759797307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1080700645132886460335472837375350229900000000000)
      constant := (16564982764530638667954997151194111789774253033093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387268904198988665759/100000000000000000000)
  centralHi := (2420430651243679161/625000000000000000)
  directionLo := (390482809133526669159/100000000000000000000)
  directionHi := (9762070228338166729/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree062.table
  base := (-860078249618493020390194215123310182731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-421291954906067186010582481541849900000000000)
      constant := (6552359204713504970284636972228719364129805345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree062.table
  base := (-860101356235596593967225546154342703457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1098412831163612516805301237388003589900000000000)
      constant := (17125215731117841978390070936430847786366867034715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390482809133526669159/100000000000000000000)
  centralHi := (9762070228338166729/2500000000000000000)
  directionLo := (196835238396313946447/50000000000000000000)
  directionHi := (78734095358525578579/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree063.table
  base := (-3951255014624397342519617946746767887047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-428085390913633033731295263213209900000000000)
      constant := (6770367499058858824581941576696854920784233553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree063.table
  base := (-1975677303021890389772006718890778876171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-62006945399685476293062757633369830550000000000)
      constant := (983052178878144666501904782238493730681227912781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196835238396313946447/50000000000000000000)
  centralHi := (78734095358525578579/20000000000000000000)
  directionLo := (396832539451416123517/100000000000000000000)
  directionHi := (198416269725708061759/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree064.table
  base := (-3582337889683736153149197975502533751711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-434878826921198881452008044884569900000000000)
      constant := (6992007927153232111722968976927412253198796089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree064.table
  base := (-447802964687014123042505395573793789113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-283459300806266157436239509353327577475000000000)
      constant := (4568538190366343466711522543843838705556857608974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396832539451416123517/100000000000000000000)
  centralHi := (198416269725708061759/50000000000000000000)
  directionLo := (399969604391114315297/100000000000000000000)
  directionHi := (199984802195557157649/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree065.table
  base := (-1596827581362626592951646472896037690991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-220836131464382364586360413277964950000000000)
      constant := (3608640166514448353042509287571371769514200809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree065.table
  base := (-159686455550706197829776300922708952399/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-287887347313947671553696609356490917475000000000)
      constant := (4715713989555521887635771344756484340331644302005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399969604391114315297/100000000000000000000)
  centralHi := (199984802195557157649/50000000000000000000)
  directionLo := (8061645105215417493/2000000000000000000)
  directionHi := (403082255260770874651/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree066.table
  base := (-2785219806287167717741307539529422431301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-448465698936330576893433608227289900000000000)
      constant := (7446184584352990232823827484182643761778298499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree066.table
  base := (-2785283504231639382159217073245820555681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-129917952809612971409401648604290781100000000000)
      constant := (2162338719182477506703773128530203120973822956391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8061645105215417493/2000000000000000000)
  centralHi := (403082255260770874651/100000000000000000000)
  directionLo := (406171053345058068451/100000000000000000000)
  directionHi := (101542763336264517113/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree067.table
  base := (-2357042827010786446525759876871504174419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-455259134943896424614146389898649900000000000)
      constant := (7678720568846764722314500156703392085916751781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree067.table
  base := (-294637210358431268227610060427766354163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-296743440329310699788610809362817597475000000000)
      constant := (5017182504637668393927991942366472495319745198874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406171053345058068451/100000000000000000000)
  centralHi := (101542763336264517113/25000000000000000000)
  directionLo := (3197160458952670701/781250000000000000)
  directionHi := (409236538745941849729/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree068.table
  base := (-95456678174157742914683452254759341379/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-115513142737865568083714792892502475000000000)
      constant := (1978722047811823430888493240248919299792964105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree068.table
  base := (-1909180794123632657260539111127622352483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (15423912)
      previous := (7711956)
      next := (7711956)
      square := (60541503243895642922822730777120000000000000)
      linear := (-4168463485633110227073604281882089100000000000)
      constant := (71577509872824647738796815559970215419440888253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3197160458952670701/781250000000000000)
  centralHi := (409236538745941849729/100000000000000000000)
  directionLo := (206139615742634197397/50000000000000000000)
  directionHi := (82455846297053678959/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree069.table
  base := (-360374984739614630351695498390509241823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-117211501739757030013892988310342475000000000)
      constant := (2038671842682365322389846929107265440224163577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree069.table
  base := (-1441540595529055706988505189237731321831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-135822014819854990232677781941841901100000000000)
      constant := (2368062141211141855040130348438398367430154569041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206139615742634197397/50000000000000000000)
  centralHi := (82455846297053678959/20000000000000000000)
  directionLo := (16611985301385660939/4000000000000000000)
  directionHi := (103824908133660380869/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree070.table
  base := (-23853716894839232362940365143912703601/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-118909860741648491944071183728182475000000000)
      constant := (2099529509679626242625157527119030215105661990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree070.table
  base := (-954183665993881652807822043805501480863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1240110319409420968563928437489230469900000000000)
      constant := (21948706596955619937541369141043925608253056712737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16611985301385660939/4000000000000000000)
  centralHi := (103824908133660380869/25000000000000000000)
  directionLo := (104574556194591688389/25000000000000000000)
  directionHi := (418298224778366753557/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree071.table
  base := (-111771369349413402123214827740377006407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-120608219743539953874249379146022475000000000)
      constant := (2161295034258486964904107251916434889157642193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree071.table
  base := (-447115584813470411368922352692355648539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1257822505440147025033756837501883829900000000000)
      constant := (22594342183378019418161005195320818923131088772261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104574556194591688389/25000000000000000000)
  centralHi := (418298224778366753557/100000000000000000000)
  directionLo := (6582429279917237857/1562500000000000000)
  directionHi := (421275473914703222849/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree072.table
  base := (19921204345714203195022846660094305767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-122306578745431415804427574563862475000000000)
      constant := (2223968404078679376722852280765687822013129167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree072.table
  base := (39829458255646672452337637102207694107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-70863038415048504527976957639696510550000000000)
      constant := (1291636994701527985160150993987781322478712211523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6582429279917237857/1562500000000000000)
  centralHi := (421275473914703222849/100000000000000000000)
  directionLo := (424231829300186472041/100000000000000000000)
  directionHi := (212115914650093236021/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree073.table
  base := (62615810326814943067113659047428670753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-248009875494645755469211539963404950000000000)
      constant := (4575099217341427272309502397710597949351756765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree073.table
  base := (125227165101859301719873949988491447711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1293246877501599137973413637527190549900000000000)
      constant := (23914077654241975319379010528088435065186589342555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424231829300186472041/100000000000000000000)
  centralHi := (212115914650093236021/50000000000000000000)
  directionLo := (427167724741356496277/100000000000000000000)
  directionHi := (213583862370678248139/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree074.table
  base := (119233089739457002524400624376546616937/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-251406593498428679329567930799084950000000000)
      constant := (4704077278304833418050823066945957060196871685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree074.table
  base := (596155869764501607176126660536283569851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-655479531766162597221621018769921954950000000000)
      constant := (12294088670969779052094923140021153972163426182651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427167724741356496277/100000000000000000000)
  centralHi := (213583862370678248139/50000000000000000000)
  directionLo := (430083579237840779723/100000000000000000000)
  directionHi := (107520894809460194931/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree075.table
  base := (444550061250842459678933425640087399561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-127401655751105801594962160817382475000000000)
      constant := (2417435487988415096315297273934983906562921761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree075.table
  base := (444545943278327164571774005144239444811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-36907534710084756969807512154236035275000000000)
      constant := (701993469198916470319939808591571192439363416179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430083579237840779723/100000000000000000000)
  centralHi := (107520894809460194931/25000000000000000000)
  directionLo := (216489898840198099837/50000000000000000000)
  directionHi := (17319191907215847987/4000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree076.table
  base := (1191881819708828336767816622810983460521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-258200029505994527050280712470444950000000000)
      constant := (4967480297572112107395209567961461042280774721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree076.table
  base := (1191874739720450334745402421512090110819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-673191717796888653691449418782575314950000000000)
      constant := (12982420118492628421486627965421797730954428474019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216489898840198099837/50000000000000000000)
  centralHi := (17319191907215847987/4000000000000000000)
  directionLo := (435856771507202333583/100000000000000000000)
  directionHi := (27241048219200145849/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree077.table
  base := (3009018954142994722413317529199492480957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-523193495019554901821274206612249900000000000)
      constant := (10203810464488988585019167013147271322798242357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree077.table
  base := (601801356739607308923709734385969392299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1364095621624503363852727237577803989900000000000)
      constant := (26667403324361729691343064306291117473314801497495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435856771507202333583/100000000000000000000)
  centralHi := (27241048219200145849/6250000000000000000)
  directionLo := (438714879321417980169/100000000000000000000)
  directionHi := (43871487932141798017/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree078.table
  base := (1826982192627502300932417899895538068223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-264993465513560374770993494141804950000000000)
      constant := (5238145770793060450928256472888255483833942823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree078.table
  base := (456744240821126910149587602121999879857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-38383550212645261675626545488623815275000000000)
      constant := (760540391850301057937586805303239831395115486546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438714879321417980169/100000000000000000000)
  centralHi := (43871487932141798017/10000000000000000000)
  directionLo := (55194310934094905387/12500000000000000000)
  directionHi := (441554487472759243097/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree079.table
  base := (863719680503109592586127314698569507977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-536780367034686597262699769954969900000000000)
      constant := (10752403810825661916004720549123337637754366885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree079.table
  base := (1079647354077185364230584547018828611231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-349879998421488869198096009400777677475000000000)
      constant := (7025248136038101566659365891163138211288648488031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55194310934094905387/12500000000000000000)
  centralHi := (441554487472759243097/100000000000000000000)
  directionLo := (55546993825703545143/12500000000000000000)
  directionHi := (88875190121125672229/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree080.table
  base := (2501459853947582539660044110213626956931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-271786901521126222491706275813164950000000000)
      constant := (5516073629483206554397949544965685208587653131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree080.table
  base := (1250727997023529059143657330535619400619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-354308044929170383315553109403941017475000000000)
      constant := (7208004650856783663099458478808573173468363203819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55546993825703545143/12500000000000000000)
  centralHi := (88875190121125672229/20000000000000000000)
  directionLo := (223589806088057497733/50000000000000000000)
  directionHi := (447179612176114995467/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree081.table
  base := (89170737505933655646265250836428741427/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-137591809762454573176031333324422475000000000)
      constant := (2828880468694232406458350576544470278460749232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree081.table
  base := (5706920569548897197478967135631322667757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-159438262860823065525782315292046381100000000000)
      constant := (3285836917331319756189516978351214742637265066373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223589806088057497733/50000000000000000000)
  centralHi := (447179612176114995467/100000000000000000000)
  directionLo := (449965804940003604709/100000000000000000000)
  directionHi := (44996580494000360471/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree082.table
  base := (257224797844378142896856101002691091777/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-557160675057384140424838114969049900000000000)
      constant := (11602527648730907024682548210978393095680429425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree082.table
  base := (6430614251504522386389960365981426959381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1452656551778133646201869237641070789900000000000)
      constant := (30322533477693847196799288963895818369259291156181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449965804940003604709/100000000000000000000)
  centralHi := (44996580494000360471/10000000000000000000)
  directionLo := (452734851413749822971/100000000000000000000)
  directionHi := (113183712853437455743/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree083.table
  base := (1793499288260479668969661111228808831969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-140988527766237497036387724160102475000000000)
      constant := (2973291143187180335396137101267624253894915769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree083.table
  base := (7173992263201758756920217201047418189959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1470368737808859702671697637653724149900000000000)
      constant := (31082022248112641476346321955578267204472962345159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452734851413749822971/100000000000000000000)
  centralHi := (113183712853437455743/25000000000000000000)
  directionLo := (227743532155116804627/50000000000000000000)
  directionHi := (91097412862046721851/20000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree084.table
  base := (3968529074727275184582514480175252776317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-285373773536257917933131839155884950000000000)
      constant := (6093716319989065172567155028841773553571209717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree084.table
  base := (1587410790251756283951618972827547637477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-165342324871065084349058448629597501100000000000)
      constant := (3538999838878023411949088770603470515335109657265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227743532155116804627/50000000000000000000)
  centralHi := (91097412862046721851/20000000000000000000)
  directionLo := (229111373475477885019/50000000000000000000)
  directionHi := (458222746950955770039/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree085.table
  base := (2179950591426021056213247059025627414869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-144385245770020420896744114995782475000000000)
      constant := (3121332961152050773726911137332487050259078669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree085.table
  base := (217994969045842518960349172070823115293/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 229522500000000000000000000000000000000000000
      center := (3855978)
      previous := (1927989)
      next := (1927989)
      square := (15135375810973910730705682694280000000000000)
      linear := (-1302589195389543093089406953009542275000000000)
      constant := (28226178519349116131252105818077580525169350370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229111373475477885019/50000000000000000000)
  centralHi := (458222746950955770039/100000000000000000000)
  directionLo := (92188438731243171679/20000000000000000000)
  directionHi := (115235548414053964599/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree086.table
  base := (9522229318750045531453394673995764855629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-584334419087647531307689241654489900000000000)
      constant := (12786862181711443708372651289380712197292271429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree086.table
  base := (9522226225496413718178800443243305259677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1523505295901037872081182837691684229900000000000)
      constant := (33417413691053448589143141245824207843187263165277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92188438731243171679/20000000000000000000)
  centralHi := (115235548414053964599/25000000000000000000)
  directionLo := (463645690114692170223/100000000000000000000)
  directionHi := (28977855632168260639/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree087.table
  base := (206886771980466827036723363195952730879/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-295563927547606689514201011662924950000000000)
      constant := (6546011823554918934238833165295275995192416975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree087.table
  base := (10344335944398324965187658383895905298807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-171246386881307103172334581967148621100000000000)
      constant := (3801650278600420458185105861914215733131454629823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463645690114692170223/100000000000000000000)
  centralHi := (28977855632168260639/6250000000000000000)
  directionLo := (116583378433434368827/25000000000000000000)
  directionHi := (466333513733737475309/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree088.table
  base := (11186129859284693953976852770646737796889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-597921291102779226749114804997209900000000000)
      constant := (13400816237261197703078308198090358572266064689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree088.table
  base := (2237225516278193208059030473728228761789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1558929667962489985020839637716990949900000000000)
      constant := (35021778808473091630214587641118106415295119704945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116583378433434368827/25000000000000000000)
  centralHi := (466333513733737475309/100000000000000000000)
  directionLo := (93801186794321248861/20000000000000000000)
  directionHi := (234502966985803122153/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree089.table
  base := (1204760280517144527600733024538499027961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-302357363555172537234913793334284950000000000)
      constant := (6856619974581364868642730108749029192921150805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree089.table
  base := (1505950106349691857565174410546290796089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-394160463498304010372667009432411077475000000000)
      constant := (8959548146670391342201238766430031203517772030578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93801186794321248861/20000000000000000000)
  centralHi := (234502966985803122153/50000000000000000000)
  directionLo := (471663212652739575373/100000000000000000000)
  directionHi := (235831606326369787687/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree090.table
  base := (3232189296794233306085686456703449367371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-152877040779477730547635092084982475000000000)
      constant := (3507323695067304127770615821358867136996551571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree090.table
  base := (1292875551058632475217173735267142429909/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-88575224445774560997805357652349870550000000000)
      constant := (2036894101978190346142974608538816463420239969505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471663212652739575373/100000000000000000000)
  centralHi := (235831606326369787687/50000000000000000000)
  directionLo := (118576401066787998429/25000000000000000000)
  directionHi := (474305604267151993717/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree091.table
  base := (6914796396922696500196574065460359937773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-309150799562738384955626575005644950000000000)
      constant := (7174490364211798883879450653917139081725222373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree091.table
  base := (13829591355733133649938031271288508781333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1612066226054668154430324837754951029900000000000)
      constant := (37499482549810807861937741229004377587356861003733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118576401066787998429/25000000000000000000)
  centralHi := (474305604267151993717/100000000000000000000)
  directionLo := (476933356254889084723/100000000000000000000)
  directionHi := (119233339063722271181/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree092.table
  base := (14750109445998218416932586109655361616457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-625095035133042617631965931682649900000000000)
      constant := (14672297791798072545598882358053325143849477857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree092.table
  base := (7375054106296038308198205148104343523547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-814889206042697105450076618883802194950000000000)
      constant := (19172179362342199276691992491333878263095911365147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476933356254889084723/100000000000000000000)
  centralHi := (119233339063722271181/25000000000000000000)
  directionLo := (239773354638227945717/50000000000000000000)
  directionHi := (95909341855291178287/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree093.table
  base := (3138061398367063726663234069512604949301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-631888471140608465352678713354009900000000000)
      constant := (14999245968844128117936987919165556115439097505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree093.table
  base := (7845152967060823745454214147801541887377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-91527255450895570409443424321125430550000000000)
      constant := (2177706797573709737956210016140210991283715372553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239773354638227945717/50000000000000000000)
  centralHi := (95909341855291178287/20000000000000000000)
  directionLo := (482145897470052590099/100000000000000000000)
  directionHi := (4821458974700525901/1000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree094.table
  base := (16650185302778979520273689009830710874917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-638681907148174313073391495025369900000000000)
      constant := (15329825258250143222940532560244043681635028317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree094.table
  base := (8325092197918066921677225943711757138431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-832601392073423161919905018896455554950000000000)
      constant := (20031286720717491708084768256926830040689319175231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482145897470052590099/100000000000000000000)
  centralHi := (4821458974700525901/1000000000000000000)
  directionLo := (30295696793524727611/6250000000000000000)
  directionHi := (484731148696395641777/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree095.table
  base := (17629744269947726256689258410158561213447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-645475343155740160794104276696729900000000000)
      constant := (15664035658905417935959313151804842982938372847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree095.table
  base := (17629743492372215846617545500617363616213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1682914970177572380309638437805564469900000000000)
      constant := (40935911977213438954585005597420782848348619902613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30295696793524727611/6250000000000000000)
  centralHi := (484731148696395641777/100000000000000000000)
  directionLo := (487302684771848943247/100000000000000000000)
  directionHi := (30456417798240558953/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree096.table
  base := (9314491900582364031127514408482903202297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-326134389581653004257408529184044950000000000)
      constant := (8000938584934828203101704659368049295566631697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree096.table
  base := (18628983134577310527526627212842326838003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-188958572912033159642162981979801981100000000000)
      constant := (4646526440144074906199450098402773368085521426267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487302684771848943247/100000000000000000000)
  centralHi := (30456417798240558953/6250000000000000000)
  directionLo := (244930360845270026343/50000000000000000000)
  directionHi := (489860721690540052687/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree097.table
  base := (9823951909209874088765503743211239733573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-329531107585435928117764920019724950000000000)
      constant := (8171674895173538104244886847529000506522178173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree097.table
  base := (1964790324704041300077230504600660403891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-859169671119512246624647618915435594950000000000)
      constant := (21355525695841911916983865228840243194037597643455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244930360845270026343/50000000000000000000)
  centralHi := (489860721690540052687/100000000000000000000)
  directionLo := (246202734918045485619/50000000000000000000)
  directionHi := (492405469836090971239/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree098.table
  base := (20686504255715913477706808647990306958513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-665855651178437703956242621710809900000000000)
      constant := (16688453519664443240072215535525289321283791113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree098.table
  base := (20686503765998221549598114286201011984553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1736051528269750549719123637843524549900000000000)
      constant := (43612852266683068993549386669869686783434759822953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246202734918045485619/50000000000000000000)
  centralHi := (492405469836090971239/100000000000000000000)
  directionLo := (30933570886471930253/6250000000000000000)
  directionHi := (494937134183550884049/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree099.table
  base := (21744785057242990352947227525337079251709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-672649087186003551676955403382169900000000000)
      constant := (17037188357252437307896805916214598645446683509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree099.table
  base := (2718098079694942627422026448234562804489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-48715658730568794616359778829338275275000000000)
      constant := (1236781682912903479940280964599801910116196343042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30933570886471930253/6250000000000000000)
  centralHi := (494937134183550884049/100000000000000000000)
  directionLo := (497455914492079399083/100000000000000000000)
  directionHi := (124363978623019849771/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree100.table
  base := (11411373087913844165812349804124746912673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-339721261596784699698834092526764950000000000)
      constant := (8694777151314921837931236025778621543256177273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree100.table
  base := (22822745816199616473591611253910028693947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1771475900331202662658780437868831269900000000000)
      constant := (45444916345020293423565594875989617065740785655547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497455914492079399083/100000000000000000000)
  centralHi := (124363978623019849771/25000000000000000000)
  directionLo := (499962005488892894121/100000000000000000000)
  directionHi := (249981002744446447061/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree101.table
  base := (5980096892904752331263783090012108501751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (164857212375408845872470920000000000000)
      linear := (-16817859994146045660189710977475000000000)
      constant := (434897347205914672886642180021237108501751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree101.table
  base := (11960193631741695909747024734252624263329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (218484)
      previous := (109242)
      next := (109242)
      square := (857587218776876816228593725840000000000000)
      linear := (-87696700635326375802794276927824950000000000)
      constant := (2273070264980422690714785159708788838208918729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499962005488892894121/100000000000000000000)
  centralHi := (249981002744446447061/50000000000000000000)
  directionLo := (100491119408990668497/20000000000000000000)
  directionHi := (251227798522476671243/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree102.table
  base := (25037709210973021095561501571042789618019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-693029395208701094839093748396249900000000000)
      constant := (18105179515190131464952488978339487296893411819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree102.table
  base := (625942723674572894770600889507424489957/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-173673613263423181045601426172062475000000000)
      constant := (4547763378252113786741360006055284509720513570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100491119408990668497/20000000000000000000)
  centralHi := (251227798522476671243/50000000000000000000)
  directionLo := (504936874342848210803/100000000000000000000)
  directionHi := (126234218585712052701/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree103.table
  base := (13087355532753415319798401254957978356573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-349911415608133471279903265033804950000000000)
      constant := (9234219390870138620895556725275933687215401173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree103.table
  base := (26174710839359399608506912066154872210153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1824612458423380832068265637906791349900000000000)
      constant := (48264168267908143085191562047646657086107419728553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504936874342848210803/100000000000000000000)
  centralHi := (126234218585712052701/25000000000000000000)
  directionLo := (253703009018640751241/50000000000000000000)
  directionHi := (507406018037281502483/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree104.table
  base := (27331393111296112616997170973609337229309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-706616267223832790280519311738969900000000000)
      constant := (18835329154796527600187409351488298449076181109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree104.table
  base := (427053014337264225695500275741464328959/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-460581161113526722134523509479861177475000000000)
      constant := (12305723446809760480149724926179243196471882946544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253703009018640751241/50000000000000000000)
  centralHi := (507406018037281502483/100000000000000000000)
  directionLo := (509863204408569572867/100000000000000000000)
  directionHi := (127465801102142393217/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree105.table
  base := (28507755328194433614105690526374510443079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-713409703231398638001232093410329900000000000)
      constant := (19205850634153368772888662476587710881029848879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree105.table
  base := (14253877581141242148927124538055901517723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-103335379471379608055995690996227670550000000000)
      constant := (2788394819156309067425378940320240081461982481347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509863204408569572867/100000000000000000000)
  centralHi := (127465801102142393217/25000000000000000000)
  directionLo := (64038575688688849657/12500000000000000000)
  directionHi := (512308605509510797257/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree106.table
  base := (7425949424813977501425814279435736704091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-180050784809741121430486218770422475000000000)
      constant := (4895000804909483950258503186357818800118432291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree106.table
  base := (29703797557166664366531257833544803982923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1877749016515559001477750837944751429900000000000)
      constant := (51168807140199608179843700996012460399312903357323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64038575688688849657/12500000000000000000)
  centralHi := (512308605509510797257/100000000000000000000)
  directionLo := (20589695572239015093/4000000000000000000)
  directionHi := (257371194652987688663/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree107.table
  base := (3091952021024553465952712888582889920729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-363498287623265166721328828376524950000000000)
      constant := (9978893455552508688433623964142947450406782645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree107.table
  base := (15459760044284602044161601626027495974619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-947730601273142528973789618978702394950000000000)
      constant := (26077997486517259976552613382386829320560366977819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20589695572239015093/4000000000000000000)
  centralHi := (257371194652987688663/50000000000000000000)
  directionLo := (25858235990577019259/5000000000000000000)
  directionHi := (517164719811540385181/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree108.table
  base := (32154922849223881378706919859643552645807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-733790011254096181163370438424409900000000000)
      constant := (20339201708432819413754093217861513080539877207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree108.table
  base := (32154922745036992044140558530020916682373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-212574820953001234935267515330006461100000000000)
      constant := (5905852249223823934147540912915147530541220335197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25858235990577019259/5000000000000000000)
  centralHi := (517164719811540385181/100000000000000000000)
  directionLo := (519575757216475439609/100000000000000000000)
  directionHi := (51957575721647543961/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree109.table
  base := (16705002803097455004655833994492495947087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-370291723630831014442041610047884950000000000)
      constant := (10362123805759686153042149435142010001156234487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree109.table
  base := (8352501379247805475466860122272054608129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-482721393651934292721809009495677877475000000000)
      constant := (13539708237471285495071013678272486016459869739329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519575757216475439609/100000000000000000000)
  centralHi := (51957575721647543961/10000000000000000000)
  directionLo := (260987829005683034909/50000000000000000000)
  directionHi := (521975658011366069819/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree110.table
  base := (2167798029550456502070328259577255462473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-186844220817306969151199000441782475000000000)
      constant := (5278231155069871068513885558500500081890748292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree110.table
  base := (693695367928769959731722908002264263817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-974298880319231613678532218997682434950000000000)
      constant := (27587241546717306247608467065456090122906699035425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260987829005683034909/50000000000000000000)
  centralHi := (521975658011366069819/100000000000000000000)
  directionLo := (524364575105644741749/100000000000000000000)
  directionHi := (2097458300422578967/400000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree111.table
  base := (7195842288420244489428525612170275428169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-754170319276793724325508783438489900000000000)
      constant := (21505232734642157979596168852197398798213759845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree111.table
  base := (7195842275345196247328378740777412689777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-218478882963243253758543648667557581100000000000)
      constant := (6244402297054034277468732608106631167970959930765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524364575105644741749/100000000000000000000)
  centralHi := (2097458300422578967/400000000000000000)
  directionLo := (131685664485320900977/25000000000000000000)
  directionHi := (526742657941283603909/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree112.table
  base := (18646667254146789012718555180337274911337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-380481877642179786023110782554924950000000000)
      constant := (10950585977274200074957250303801534941370548737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree112.table
  base := (37293334452333879700736338013801820962811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-1984022132699915340296721238020671589900000000000)
      constant := (57234245689893774444883831996394706107843892663611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131685664485320900977/25000000000000000000)
  centralHi := (526742657941283603909/100000000000000000000)
  directionLo := (529110052601888164689/100000000000000000000)
  directionHi := (52911005260188816469/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree113.table
  base := (7725427533319199589629607817625355172367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-767757191291925419766934346781209900000000000)
      constant := (22300742279949364593875138907920344940566578835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree113.table
  base := (386271376186996049657845123744238608413/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-500433579682660349191637409508331237475000000000)
      constant := (14569589535633988021950840125857490449044726370325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529110052601888164689/100000000000000000000)
  centralHi := (52911005260188816469/10000000000000000000)
  directionLo := (531466901917417260231/100000000000000000000)
  directionHi := (66433362739677157529/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree114.table
  base := (4997577614132563563317733417976021191431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-193637656824872816871911782113142475000000000)
      constant := (5675985927701194507918823210307111434347575262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree114.table
  base := (39980620872068778642236098231920902661519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-224382944973485272581819782005108701100000000000)
      constant := (6592439781257025250143171101376667543656494887191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531466901917417260231/100000000000000000000)
  centralHi := (66433362739677157529/12500000000000000000)
  directionLo := (533813345564741736313/100000000000000000000)
  directionHi := (266906672782370868157/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree115.table
  base := (10338446061112184278596578431065554328001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-195336015826764278802089977530982475000000000)
      constant := (5777694061770401456140701726232678094699938201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree115.table
  base := (10338446052342251183908920895682003097521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-509289672698023377426551609514657917475000000000)
      constant := (15098761339036020165956321918302811178186658286321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533813345564741736313/100000000000000000000)
  centralHi := (266906672782370868157/50000000000000000000)
  directionLo := (268074760082121090783/50000000000000000000)
  directionHi := (536149520164242181567/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree116.table
  base := (42746627658121062506142199665122638321539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-788137499314622962929072691795289900000000000)
      constant := (23521239888752921196007915938492044433518019339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree116.table
  base := (5343328453512868037509491375908335046339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-513717719205704891544008709517821257475000000000)
      constant := (15366905029240562732033073659425035538776676931078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268074760082121090783/50000000000000000000)
  centralHi := (536149520164242181567/100000000000000000000)
  directionLo := (107695111874526949921/20000000000000000000)
  directionHi := (269237779686317374803/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree117.table
  base := (22079575575971342516728151304242096630003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-397465467661094405324892736733324950000000000)
      constant := (11967667317898473527398884359299625277722660603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree117.table
  base := (22079575563128877539323310694901844168521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-115143503491863645702547957671329910550000000000)
      constant := (3474982350761907316731253949288475265035430906369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107695111874526949921/20000000000000000000)
  centralHi := (269237779686317374803/50000000000000000000)
  directionLo := (21631663758888141483/4000000000000000000)
  directionHi := (135197898493050884269/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree118.table
  base := (45591354724204048021320990550802422349423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-801724371329754658370498255138009900000000000)
      constant := (24353060488196244213290612391184173710386464023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree118.table
  base := (22795677351114202601363349134572303339687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1045147624442135839557845819048295874950000000000)
      constant := (31820615973178868495873668193096923268098550573287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21631663758888141483/4000000000000000000)
  centralHi := (135197898493050884269/25000000000000000000)
  directionLo := (543097751956608090229/100000000000000000000)
  directionHi := (54309775195660809023/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree119.table
  base := (4704323837355343063462599783986033585467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-404258903668660253045605518404684950000000000)
      constant := (12387208722968511883623743568164274193026744335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree119.table
  base := (9408647670950549717380572435343351971319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (15423912)
      previous := (7711956)
      next := (7711956)
      square := (60541503243895642922822730777120000000000000)
      linear := (-7294143373408296662925674872350329100000000000)
      constant := (224021692092937641968752216114709248780674130355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543097751956608090229/100000000000000000000)
  centralHi := (54309775195660809023/10000000000000000000)
  directionLo := (68174269826678168233/12500000000000000000)
  directionHi := (109078831722685069173/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree120.table
  base := (48514802098939863173570717049917404145799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-815311243344886353811923818480729900000000000)
      constant := (25199405509008564774760726957682395439691295599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree120.table
  base := (48514802082856570716603451540604464190929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-236191068993969310228372048680210941100000000000)
      constant := (7316977057688023074775810200370771981232171684681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68174269826678168233/12500000000000000000)
  centralHi := (109078831722685069173/20000000000000000000)
  directionLo := (17115029268861769641/3125000000000000000)
  directionHi := (547680936603576628513/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree121.table
  base := (12501511474891199026206924987042785415593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-205526169838113050383159150038022475000000000)
      constant := (6407006169350680308010214638955724179024464193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree121.table
  base := (25003022942903542907322905663057531259739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1071715903488224924262588419067275914950000000000)
      constant := (33486402729668990782292211349032311483978434198939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17115029268861769641/3125000000000000000)
  centralHi := (547680936603576628513/100000000000000000000)
  directionLo := (549958206037782183533/100000000000000000000)
  directionHi := (274979103018891091767/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree122.table
  base := (5151696977484119203200907000794799249551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-414449057680009024626674690911724950000000000)
      constant := (13030137475556752385303664601150727635723348755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree122.table
  base := (25758484881536798648983788567428478434843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1080571996503587952497502619073602594950000000000)
      constant := (34051152417641109668473004728080994659569480785243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549958206037782183533/100000000000000000000)
  centralHi := (274979103018891091767/50000000000000000000)
  directionLo := (69028260568772260893/12500000000000000000)
  directionHi := (110445216910035617429/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree123.table
  base := (53047573724358911651942478598550778125557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-835691551367583896974062163494809900000000000)
      constant := (26496156330136731559428477768736329187658806957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree123.table
  base := (26523786857147114639566370838721047412609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-121047565502105664525824091008881030550000000000)
      constant := (3846738424834184411619945227554731348783091054201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69028260568772260893/12500000000000000000)
  centralHi := (110445216910035617429/20000000000000000000)
  directionLo := (554484687369223204519/100000000000000000000)
  directionHi := (13862117184230580113/2500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree124.table
  base := (54597857747855435995204834854983027839203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-842484987375149744694774945166169900000000000)
      constant := (26935668814469723642497219305213689466987709803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree124.table
  base := (27298928869623901478502197234324344292283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1098284182534314008967331019086255954950000000000)
      constant := (35194882947265706644053726198937472354112630674683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554484687369223204519/100000000000000000000)
  centralHi := (13862117184230580113/2500000000000000000)
  directionLo := (556734127386017133501/100000000000000000000)
  directionHi := (278367063693008566751/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree125.table
  base := (28083910922595556272690920517894136117219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-424639211691357796207743863418764950000000000)
      constant := (13689406202055528212246805780236469332531751019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree125.table
  base := (28083910918915036298158739585612062933707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1107140275549677037202245219092582634950000000000)
      constant := (35773863788913867521221218969890609080582024023307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556734127386017133501/100000000000000000000)
  centralHi := (278367063693008566751/50000000000000000000)
  directionLo := (558974515220143744333/100000000000000000000)
  directionHi := (279487257610071872167/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree126.table
  base := (57757466016328236104485963569115804778203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-856071859390281440136200508508889900000000000)
      constant := (27825587099060345274692983704547627724542448803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree126.table
  base := (5775746601003365524953330823589199945827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-123999596507226673937462157677656590550000000000)
      constant := (4039732038716893821215896293619880890570465873015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558974515220143744333/100000000000000000000)
  centralHi := (279487257610071872167/50000000000000000000)
  directionLo := (112241191856629795531/20000000000000000000)
  directionHi := (70150744910393622207/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree127.table
  base := (29683395130656689929450021325079797213537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-431432647698923643928456645090124950000000000)
      constant := (14137996449659032643084813545134465161375290937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree127.table
  base := (742084878199138620962575988862467482229/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-562426230790201546836036809552617997475000000000)
      constant := (18473028312940599790732950761090860186292811868580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112241191856629795531/20000000000000000000)
  centralHi := (70150744910393622207/12500000000000000000)
  directionLo := (563428565839755968131/100000000000000000000)
  directionHi := (140857141459938992033/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree128.table
  base := (60995794580262480832569178303057442314971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-869658731405413135577626071851609900000000000)
      constant := (28730029804885399132504805682983076169055019171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree128.table
  base := (60995794575660545830153462403915042387239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2267417109191532243813975638223125349900000000000)
      constant := (75078537242406332221404591939666191667767177326439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563428565839755968131/100000000000000000000)
  centralHi := (140857141459938992033/25000000000000000000)
  directionLo := (113128487813383059211/20000000000000000000)
  directionHi := (70705304883364412007/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree129.table
  base := (62644478973348259194408494173038733902841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-876452167412978983298338853522969900000000000)
      constant := (29187697815764108732141622658995050224542881041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree129.table
  base := (62644478969413779115301730256399892015583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-253903255024695366698200448692864301100000000000)
      constant := (8474938740982330640593469898968437796277328070887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113128487813383059211/20000000000000000000)
  centralHi := (70705304883364412007/12500000000000000000)
  directionLo := (113569536222156642427/20000000000000000000)
  directionHi := (70980960138847901517/12500000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree130.table
  base := (32156421720394807376752649707326754245071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-441622801710272415509525817597164950000000000)
      constant := (14824498465978213541016288829495208720053969271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree130.table
  base := (64312843437425985436350487518751908346343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2302841481252984356753632438248432069900000000000)
      constant := (77479847531072570200855897837037395495773757896743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113569536222156642427/20000000000000000000)
  centralHi := (70980960138847901517/12500000000000000000)
  directionLo := (570044392141716011203/100000000000000000000)
  directionHi := (142511098035429002801/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree131.table
  base := (16500221995710674539574615544384845697807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-222509759857027669684941104216422475000000000)
      constant := (7528481788366241793735598894240907785963329207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree131.table
  base := (66000887979967265404357923943897405485847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2320553667283710413223460838261085429900000000000)
      constant := (78694733829108282053711783526765190715447286767447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570044392141716011203/100000000000000000000)
  centralHi := (142511098035429002801/25000000000000000000)
  directionLo := (143058167601841082497/25000000000000000000)
  directionHi := (572232670407364329989/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree132.table
  base := (33854306299896700141042252241915673403847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-448416237717838263230238599268524950000000000)
      constant := (15291244240146322691834787117031245184392643247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree132.table
  base := (3385430629866772526405793777506021781047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-64951829258734346380369145507603855275000000000)
      constant := (2219975210082111489668421935983252470657325345915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143058167601841082497/25000000000000000000)
  centralHi := (572232670407364329989/100000000000000000000)
  directionLo := (11488252245678939901/2000000000000000000)
  directionHi := (574412612283946995051/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree133.table
  base := (555488138335608338177127692209892690543/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-903625911443242374181189980208409900000000000)
      constant := (31054680912442617093237491766787801117028642875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree133.table
  base := (69436017289850081871636121066580316854901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2355978039345162526163117638286392149900000000000)
      constant := (81152968732624243243372869129609907264953034107701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11488252245678939901/2000000000000000000)
  centralHi := (574412612283946995051/100000000000000000000)
  directionLo := (576584312325780133133/100000000000000000000)
  directionHi := (288292156162890066567/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree134.table
  base := (71183102059643081820015281987310291154031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-910419347450808221901902761879769900000000000)
      constant := (31530504449918222699557623699150308880062270231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree134.table
  base := (35591551028923681804159942814975204536001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1186845112687944291316473019149522754950000000000)
      constant := (41198158669060945669034523014555598869563011868801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576584312325780133133/100000000000000000000)
  centralHi := (288292156162890066567/50000000000000000000)
  directionLo := (72343482914141695343/12500000000000000000)
  directionHi := (115749572662626712549/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree135.table
  base := (729498669032106792725579547384195643337/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-229303195864593517405653885887782475000000000)
      constant := (8002489773180735594832047967031707368942018425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree135.table
  base := (72949866901675940987695358348749204477337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-265711379045179404344752715367966541100000000000)
      constant := (9294350375495356494130783019934183213853387958993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72343482914141695343/12500000000000000000)
  centralHi := (115749572662626712549/20000000000000000000)
  directionLo := (580903356298482998639/100000000000000000000)
  directionHi := (7261291953731037483/1250000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree136.table
  base := (4671019488937811937981587538807993163313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-231001554866484979335832081305622475000000000)
      constant := (8123261210215089569690131425680027953035823652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree136.table
  base := (74736311821693375197065568969029052951649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918090000000000000000000000000000000000000000
      center := (15423912)
      previous := (7711956)
      next := (7711956)
      square := (60541503243895642922822730777120000000000000)
      linear := (-8336036669333358808209698402506409100000000000)
      constant := (293811338604299936576210752925426810922437943041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580903356298482998639/100000000000000000000)
  centralHi := (7261291953731037483/1250000000000000000)
  directionLo := (583050880651223307119/100000000000000000000)
  directionHi := (7288136008140291339/1250000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree137.table
  base := (76542436819384077691211515844146673161377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-930799655473505765064041106893849900000000000)
      constant := (32979761694334122974705980698161341512919206777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree137.table
  base := (7654243681826320707318574869237844562877/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1213413391734033376021215619168502794950000000000)
      constant := (43091643884842478382394813656207017176991237142385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583050880651223307119/100000000000000000000)
  centralHi := (7288136008140291339/1250000000000000000)
  directionLo := (585190524100904937657/100000000000000000000)
  directionHi := (292595262050452468829/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree138.table
  base := (78368241892710332158064846508775524557509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-937593091481071612784753888565209900000000000)
      constant := (33470109653147933236474275013223755326011149309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree138.table
  base := (19592060472938129532269543623816874472929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-67903860263855355792007212176379415275000000000)
      constant := (2429571836627632595297416814274674171410522782681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585190524100904937657/100000000000000000000)
  centralHi := (292595262050452468829/50000000000000000000)
  directionLo := (23492894911162108559/4000000000000000000)
  directionHi := (73415296597381589247/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree139.table
  base := (2005343176083708654745345529374315153357/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-236096631872159365126366667559142475000000000)
      constant := (8491022179326377066207246041912381663793947570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree139.table
  base := (80213727042529911358544874383788301889857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2462251155529518864982088038362312309900000000000)
      constant := (88755371903381911738159595042353124075646499699457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23492894911162108559/4000000000000000000)
  centralHi := (73415296597381589247/12500000000000000000)
  directionLo := (294723255629811692529/50000000000000000000)
  directionHi := (589446511259623385059/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree140.table
  base := (10259861533957893472581675793322281258737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-237794990874050827056544862976982475000000000)
      constant := (8615424721702642927584722753686082682240752274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree140.table
  base := (820788922709638461477113566455187070269/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-619990835390061230362979109593741417475000000000)
      constant := (22513911281014036986679011692556687479705509836725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294723255629811692529/50000000000000000000)
  centralHi := (589446511259623385059/100000000000000000000)
  directionLo := (591563022598155703677/100000000000000000000)
  directionHi := (295781511299077851839/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree141.table
  base := (83963737578018750935364285641860486803697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-957973399503769155946892233579289900000000000)
      constant := (34962940161666836879866763308098119725884513097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree141.table
  base := (2623866799294414740089943405937398771381/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-69379875766415860497826245510767195275000000000)
      constant := (2537927938350756062392044038520370736483424727272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591563022598155703677/100000000000000000000)
  centralHi := (295781511299077851839/50000000000000000000)
  directionLo := (593671988369664308039/100000000000000000000)
  directionHi := (14841799709241607701/2500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree142.table
  base := (17173652592555393780962945035900747855687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-964766835511335003667605015250649900000000000)
      constant := (35467812541877994630384708230387593444379315435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree142.table
  base := (10733532870283313971465609283025650934123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-628846928405424258597893309600068097475000000000)
      constant := (23171163468276197291860233353172710118148599337046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593671988369664308039/100000000000000000000)
  centralHi := (14841799709241607701/2500000000000000000)
  directionLo := (119154697741065264491/20000000000000000000)
  directionHi := (74471686088165790307/12500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree143.table
  base := (87792468426296449280504217719991492861301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-971560271518900851388317796922009900000000000)
      constant := (35976316027447703525973612107262443918678131501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree143.table
  base := (17558493685172072244686166144397823662591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2533099899652423090861401638412925749900000000000)
      constant := (94013389401498433607571881325924270547938090736955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119154697741065264491/20000000000000000000)
  centralHi := (74471686088165790307/12500000000000000000)
  directionLo := (59786760232800735763/10000000000000000000)
  directionHi := (597867602328007357631/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree144.table
  base := (89736353968931895742824493520028215061557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-978353707526466699109030578593369900000000000)
      constant := (36488450618379581898877150979071313421842942957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree144.table
  base := (89736353968559360060092051137984946772083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-283423565075905460814581115380619901100000000000)
      constant := (10594623596201956841329026411735611512144363399387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59786760232800735763/10000000000000000000)
  centralHi := (597867602328007357631/100000000000000000000)
  directionLo := (119990881317334294589/20000000000000000000)
  directionHi := (299977203293335736473/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree145.table
  base := (91699919591033446661654278075601322712241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-985147143534032546829743360264729900000000000)
      constant := (37004216314677201510606457724598769592987570441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree145.table
  base := (45849959795357608512223727265834863906007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1284262135856937601900529219219116234950000000000)
      constant := (48349661383035827439345027242539219474692666435607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119990881317334294589/20000000000000000000)
  centralHi := (299977203293335736473/50000000000000000000)
  directionLo := (301016988744858827513/50000000000000000000)
  directionHi := (602033977489717655027/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree146.table
  base := (46841582646473092664817961705822867517733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-495970289770799197275228070968044950000000000)
      constant := (18761806558172041277914888488425586771548394333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree146.table
  base := (46841582646337179124730029050363503285711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1293118228872300630135443419225442914950000000000)
      constant := (49028260301134877591702719469981895866167616106511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301016988744858827513/50000000000000000000)
  centralHi := (602033977489717655027/100000000000000000000)
  directionLo := (30205319486864173121/5000000000000000000)
  directionHi := (604106389737283462421/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree147.table
  base := (23921522768752440123190506851086095602543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-249683503887291060567792230901862475000000000)
      constant := (9511660255845922447851244806690866836241541143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree147.table
  base := (95686091074777580684211012100343728080549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-289327627086147479637857248718171021100000000000)
      constant := (11047022874935661642637640929205392932048257620861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30205319486864173121/5000000000000000000)
  centralHi := (604106389737283462421/100000000000000000000)
  directionLo := (75771464594069334943/12500000000000000000)
  directionHi := (121234343350510935909/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree148.table
  base := (48854348468779049567786849545597937214257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-502763725778365044995940852639404950000000000)
      constant := (19286650017899714803250684163813587157522635657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree148.table
  base := (6106793558584987064377281548224935239847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-655415207451513343302635909619048137475000000000)
      constant := (25199844645633534936403941067607940986751990885788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75771464594069334943/12500000000000000000)
  centralHi := (121234343350510935909/20000000000000000000)
  directionLo := (304115015356059054133/50000000000000000000)
  directionHi := (608230030712118108267/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree149.table
  base := (49875491440459598134569375889413722190999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-506160443782147968856297243475084950000000000)
      constant := (19551795076797323939113423521491599430070380799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree149.table
  base := (99750982880749829617518420165507935631727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2639373015836779429680372038488845909900000000000)
      constant := (102185038726618034964891724006444135135762421777327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304115015356059054133/50000000000000000000)
  centralHi := (608230030712118108267/100000000000000000000)
  directionLo := (610281402575392997613/100000000000000000000)
  directionHi := (305140701287696498807/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree150.table
  base := (50906474452707484417611166723318064820933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-509557161785930892716653634310764950000000000)
      constant := (19818755688386314240652180823684685079238337533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree150.table
  base := (50906474452635162461154904969741817613167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-147615844548194749230566691027861070550000000000)
      constant := (5754454794815622268772493851975250502220383887863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610281402575392997613/100000000000000000000)
  centralHi := (305140701287696498807/50000000000000000000)
  directionLo := (306162951056587532929/50000000000000000000)
  directionHi := (612325902113175065859/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree151.table
  base := (51947297505680581422159061351665648074763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-512953879789713816577010025146444950000000000)
      constant := (20087531852668296170393479078136566226010657363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree151.table
  base := (10389459501123763833814821281645266714521/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1337398693949115771310014419257076314950000000000)
      constant := (52492410661366015632746889509464045697529047516605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306162951056587532929/50000000000000000000)
  centralHi := (612325902113175065859/100000000000000000000)
  directionLo := (614363597935325600349/100000000000000000000)
  directionHi := (12287271958706512007/2000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree152.table
  base := (105995921199067304563307623199338560205799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1032701195586993480874732831964249900000000000)
      constant := (40716247139289696934123094788432477452659355599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree152.table
  base := (105995921198961820451623634134806044319653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2692509573928957599089857238526805989900000000000)
      constant := (106398943774778752758172318936797348607330533438053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614363597935325600349/100000000000000000000)
  centralHi := (12287271958706512007/2000000000000000000)
  directionLo := (616394557517636724267/100000000000000000000)
  directionHi := (154098639379409181067/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree153.table
  base := (54058463734418344003487933928353367323281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-519747315797279664297722806817804950000000000)
      constant := (20630530839317518081778796832342612550064789481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree153.table
  base := (108116927468746613440131326029538949064499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1041992218362046772610413548073609900000000000)
      constant := (41454268997627614166354726648367909644406954299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616394557517636724267/100000000000000000000)
  centralHi := (154098639379409181067/25000000000000000000)
  directionLo := (9662794487935978003/1562500000000000000)
  directionHi := (618418847227902592193/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree154.table
  base := (13782201727620799025736985517002196173521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-261572016900531294079039598826742475000000000)
      constant := (10452376830843910133070332559539192456332175442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree154.table
  base := (5512880691044473968997354728208838238711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-681983486497602428007378509638028177475000000000)
      constant := (27313912746722984708279406757287239221107047297555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9662794487935978003/1562500000000000000)
  centralHi := (618418847227902592193/100000000000000000000)
  directionLo := (38777283271951563371/6250000000000000000)
  directionHi := (620436532351225013937/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree155.table
  base := (56208990127873661377389032528016436501611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-526540751804845512018435588489164950000000000)
      constant := (21180792036757238784132972614015750418752933811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree155.table
  base := (56208990127840825618866202272460076379429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1372823066010567884249671219282383034950000000000)
      constant := (55349117873487011571904168133550423008957690150629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38777283271951563371/6250000000000000000)
  centralHi := (620436532351225013937/100000000000000000000)
  directionLo := (622447677114580805151/100000000000000000000)
  directionHi := (19451489909830650161/3125000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree156.table
  base := (114598026773464273018661773650743139971541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1059874939617256871757583958649689900000000000)
      constant := (42917291929054452448628205176619155170849689741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree156.table
  base := (114598026773408202153325826505049994585923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-307039813116873536107685648730824381100000000000)
      constant := (12461145327009249018627839298927178432588819151147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622447677114580805151/100000000000000000000)
  centralHi := (19451489909830650161/3125000000000000000)
  directionLo := (3122261723553385101/500000000000000000)
  directionHi := (624452344710677020201/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree157.table
  base := (29199438343599000278348563471045280916487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-266667093906205679869574185080262475000000000)
      constant := (10869157722499602196226966954899207735629083887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree157.table
  base := (23359550674869625865513857754480532363083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2781070504082587881438999238590072789900000000000)
      constant := (113611867575226995481853775215658981717743704927415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3122261723553385101/500000000000000000)
  centralHi := (624452344710677020201/100000000000000000000)
  directionLo := (626450597321119134689/100000000000000000000)
  directionHi := (62645059732111913469/10000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree158.table
  base := (119017160058815319402129563407108588795261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1073461811632388567199009521992409900000000000)
      constant := (44039600956349129536021467699059948914300457461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree158.table
  base := (11901716005877444942579109084862933341177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1399391345056656968954413819301363074950000000000)
      constant := (57541457321706264991634420106694841697063572233885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626450597321119134689/100000000000000000000)
  centralHi := (62645059732111913469/10000000000000000000)
  directionLo := (628442496138916208839/100000000000000000000)
  directionHi := (15711062403472905221/2500000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree159.table
  base := (60628123413494596889210000853844059441807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-540127623819977207459861151831884950000000000)
      constant := (22303101064054669010524565911043627800365873207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree159.table
  base := (121256246826954302912073681030883483818179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-312943875127115554930961782068375501100000000000)
      constant := (12951494349738548072963143992421985880701051509931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628442496138916208839/100000000000000000000)
  centralHi := (15711062403472905221/2500000000000000000)
  directionLo := (63042810139034607579/10000000000000000000)
  directionHi := (630428101390346075791/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree160.table
  base := (123515013679178850453565221397675161773223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1087048683647520262640435085335129900000000000)
      constant := (45176434405281699008572327944971268325248647823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree160.table
  base := (61757506839574532577844756207981240518503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 132664005000000000000000000000000000000000000000
      center := (2228755284)
      previous := (1114377642)
      next := (1114377642)
      square := (8748247218742920402347884597293840000000000000)
      linear := (-1417103531087383025424242219314016434950000000000)
      constant := (59026735543968569261355674941841354308410576916903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63042810139034607579/10000000000000000000)
  centralHi := (630428101390346075791/100000000000000000000)
  directionLo := (39525467022262666143/6250000000000000000)
  directionHi := (632407472356202658289/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree161.table
  base := (3931045644238746510740581303595381220697/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-273460529913771527590286966751622475000000000)
      constant := (11437574446967204965783633167329661595658640776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree161.table
  base := (125793460615614462511060783704792575172589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2851919248205492107318312838640686229900000000000)
      constant := (119552980464289932717870341737158325175356844591789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525467022262666143/6250000000000000000)
  centralHi := (632407472356202658289/100000000000000000000)
  directionLo := (31719033369622331033/5000000000000000000)
  directionHi := (634380667392446620661/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree162.table
  base := (128091587636622395471201418861293942755977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1100635555662651958081860648677849900000000000)
      constant := (46327792275873251732652057393660633310053721377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree162.table
  base := (64045793818300345938217056525385386249099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (247639476)
      previous := (123819738)
      next := (123819738)
      square := (972027468749213378038653844143760000000000000)
      linear := (-159423968568678786877118957702963310550000000000)
      constant := (6725665404261775203703181458922877380186720021811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31719033369622331033/5000000000000000000)
  centralHi := (634380667392446620661/100000000000000000000)
  directionLo := (318173871975139854031/50000000000000000000)
  directionHi := (636347743950279708063/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree163.table
  base := (130409394742371068064411334755833321974547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1107428991670217805802573430349209900000000000)
      constant := (46908917869297490763350174607237364417462353947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree163.table
  base := (130409394742352542492759655025934234612059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2887343620266944220257969638665992949900000000000)
      constant := (122580461525209696313289194956222213794124073647259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318173871975139854031/50000000000000000000)
  centralHi := (636347743950279708063/100000000000000000000)
  directionLo := (638308758595662309649/100000000000000000000)
  directionHi := (12766175171913246193/2000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree164.table
  base := (132746881933125331266838111421774259440091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1713768)
      previous := (856884)
      next := (856884)
      square := (6726833693766182546980303419680000000000000)
      linear := (-1114222427677783653523286212020569900000000000)
      constant := (47493674568143979331117827392446522820548368291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree164.table
  base := (26549376386621903792063163888534483774737/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2905055806297670276727798038678646309900000000000)
      constant := (124108433209789515385663899416138164834264128241685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638308758595662309649/100000000000000000000)
  centralHi := (12766175171913246193/2000000000000000000)
  directionLo := (640263767028293004403/100000000000000000000)
  directionHi := (160065941757073251101/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree165.table
  base := (8246096753486295200113871233158925087/610351562500000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-280253965921337375310999748422982475000000000)
      constant := (12020515593103776820032092972735029006951946752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree165.table
  base := (33776012302276491158151179173239094390543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (123819738)
      previous := (61909869)
      next := (61909869)
      square := (486013734374606689019326922071880000000000000)
      linear := (-81187999786899898144378512185869435275000000000)
      constant := (3490163675846045240815153438568606830323971522327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640263767028293004403/100000000000000000000)
  centralHi := (160065941757073251101/25000000000000000000)
  directionLo := (20069150753127128311/3125000000000000000)
  directionHi := (642212824100068105953/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree166.table
  base := (68740448285291351577337038145155627483493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-563904649846457674482355887681644950000000000)
      constant := (24337040641056606580609889833830169255959112093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree166.table
  base := (34370224142642796175049146476608144930537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-735120044589780597416863709675988257475000000000)
      constant := (31798209721805030068330933826141644982458597044137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20069150753127128311/3125000000000000000)
  centralHi := (642212824100068105953/100000000000000000000)
  directionLo := (644155983833038514083/100000000000000000000)
  directionHi := (161038995958259628521/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree167.table
  base := (4371169500554356211827953538807889160779/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-283650683925120299171356139258662475000000000)
      constant := (12317432824310146365978203076538246293632852632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree167.table
  base := (3496935600443239210149047688167451294771/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66332002500000000000000000000000000000000000000
      center := (1114377642)
      previous := (557188821)
      next := (557188821)
      square := (4374123609371460201173942298646920000000000000)
      linear := (-739548091097462111534320809679151597475000000000)
      constant := (32187318220020735968181539272703179643857262835710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (644155983833038514083/100000000000000000000)
  centralHi := (161038995958259628521/25000000000000000000)
  directionLo := (646093299436880503863/100000000000000000000)
  directionHi := (80761662429610062983/12500000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree168.table
  base := (71146815775404549663622638466207490995899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (856884)
      previous := (428442)
      next := (428442)
      square := (3363416846883091273490151709840000000000000)
      linear := (-570698085854023522203068669353004950000000000)
      constant := (24934506208899731918554986791306874215649165699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree168.table
  base := (142293631550800709941258571634110656667033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (495278952)
      previous := (247639476)
      next := (247639476)
      square := (1944054937498426756077307688287520000000000000)
      linear := (-330656061157841611400790182081028861100000000000)
      constant := (14479466034339102879614760440498919001502856649937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell075.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646093299436880503863/100000000000000000000)
  centralHi := (80761662429610062983/12500000000000000000)
  directionLo := (129604964665179287397/20000000000000000000)
  directionHi := (324012411662948218493/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 51
  qDenominator := 101
  table := BinomialMassData.Q51_101.Degree169.table
  base := (3618237979250167175910504706350132919799/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (428442)
      previous := (214221)
      next := (214221)
      square := (1681708423441545636745075854920000000000000)
      linear := (-287047401928903223031712530094342475000000000)
      constant := (12617981160948010073623883990990496584148695990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q51_101.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 10429
  qDenominator := 20604
  table := BinomialMassData.Q10429_20604.Degree169.table
  base := (144729519169999527663324824686946885283347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 265328010000000000000000000000000000000000000000
      center := (4457510568)
      previous := (2228755284)
      next := (2228755284)
      square := (17496494437485840804695769194587680000000000000)
      linear := (-2993616736451300559076940038741913109900000000000)
      constant := (131890603174132768790747645228465642181017874564947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q10429_20604.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell075.Kernel169
