import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell099.Parameters
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch000_049
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch050_099
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch100_149
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch150_199
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch000_049
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch050_099
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch100_149
import ForestUnimodality.BinomialMassData.Q11153_21528.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree000.table
  base := (739312972822115023652145279/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (358537756603837728941464035000000000000)
      linear := (-14974167661322957366409891500000000000)
      constant := (369656486411057511826072639500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree000.table
  base := (739312972822115023652145279/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (358537756603837728941464035000000000000)
      linear := (-14974167661322957366409891500000000000)
      constant := (369656486411057511826072639500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree001.table
  base := (25832937045115334675944312270251625393949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-34513502045203022921582234168139625000000000)
      constant := (18485199797036412656829795046282663787724226392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree001.table
  base := (20648122681141965091480854734977429077701/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-932869581369461751516659363912879250000000000)
      constant := (498660968728953328230087289462896969436522717270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24983669341130349117/50000000000000000000)
  directionHi := (9993467736452139647/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree002.table
  base := (245870993086804103317231914566120818598271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-406129791163896672789900345757726500000000000)
      constant := (66157662189369922637073985340543500066762077013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree002.table
  base := (245497806202322041453390969598007239074837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-3659188225070990585644859277311976000000000000)
      constant := (594522398128300597903932963356040833749296571199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24983669341130349117/50000000000000000000)
  centralHi := (9993467736452139647/20000000000000000000)
  directionLo := (70664488040142854927/100000000000000000000)
  directionHi := (4416530502508928433/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree003.table
  base := (156844102786520432341256054937534547241901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-201726190018858402683435762168871750000000000)
      constant := (14180684510486128643320974589033488456410691301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree003.table
  base := (156548229255657241133400950851618055242307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-605848587489228629806266647422021500000000000)
      constant := (42463754117561325212342589656498226926402464321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70664488040142854927/100000000000000000000)
  centralHi := (4416530502508928433/6250000000000000000)
  directionLo := (21636492329169310839/25000000000000000000)
  directionHi := (86545969316677243357/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree004.table
  base := (2679808882239933983809998800519441252949/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-134037891491542290551785704542584000000000000)
      constant := (4931663637143933485478265364666655161597870980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree004.table
  base := (21394872102759001494771742655231846783141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-7246086349735124750867940376284411000000000000)
      constant := (265800454839346746455750063968669019125044453035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21636492329169310839/25000000000000000000)
  centralHi := (86545969316677243357/100000000000000000000)
  directionLo := (99934677364521396469/100000000000000000000)
  directionHi := (9993467736452139647/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree005.table
  base := (19440787763980453345117787441449039292537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-501638063920966139285560584002196375000000000)
      constant := (11082331204564310806187731656624635968408852022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree005.table
  base := (15520766000368236134587463357470361598633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-9039535412067191833479480925770628500000000000)
      constant := (199123617172796211465968717233780917788967492455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99934677364521396469/100000000000000000000)
  centralHi := (9993467736452139647/10000000000000000000)
  directionLo := (111730365948289686319/100000000000000000000)
  directionHi := (1396629574353621079/1250000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree006.table
  base := (29534614488418529887916807597076392054477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-200387484455768468971921351458880250000000000)
      constant := (2953597233188064304207367364988778885437298277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree006.table
  base := (11790006560018264220771725236508314017117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-401221647199972552447815610194698000000000000)
      constant := (5897935220921663464842677071926020032221384585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/100000000000000000000)
  centralHi := (1396629574353621079/1250000000000000000)
  directionLo := (122394483576370702977/100000000000000000000)
  directionHi := (61197241788185351489/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree007.table
  base := (46342450850311115106008852087175060121459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-467124561875763116363978349834056750000000000)
      constant := (4993971940887769832978261565571174135856056059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree007.table
  base := (46249966273747456373474062206027092957567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-12626433536731325998702562024743063500000000000)
      constant := (134665291854666367402264099474281879368735078909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122394483576370702977/100000000000000000000)
  centralHi := (61197241788185351489/50000000000000000000)
  directionLo := (13220115182899967471/10000000000000000000)
  directionHi := (132201151828999674711/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree008.table
  base := (9282507476615127053043579450151992986731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-800211232259983942176170995125529500000000000)
      constant := (6643907454845168009118761214387345950040428786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree008.table
  base := (4631947575523518628876948194709863811813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-7209941299531696540657051287114640500000000000)
      constant := (59738785546303522261514554415452662241108553404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/10000000000000000000)
  centralHi := (132201151828999674711/100000000000000000000)
  directionLo := (28265795216057141971/20000000000000000000)
  directionHi := (4416530502508928433/3125000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree009.table
  base := (30127043413782570959246348323396238701649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-599823747804215473204249643666649250000000000)
      constant := (4096432156284085093772857815786374097103622249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree009.table
  base := (3758160942856212320783941961849873793313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-300246882618434447480104502291027750000000000)
      constant := (2047023700397058766696011612575439127358902052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28265795216057141971/20000000000000000000)
  centralHi := (4416530502508928433/3125000000000000000)
  directionLo := (9368876002923880919/6250000000000000000)
  directionHi := (29980403209356418941/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree010.table
  base := (12303345039309314384676250583072969763419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-333086670384220825812192645291472750000000000)
      constant := (1965238368797654965061469176580649304194422019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree010.table
  base := (3069297198160178153891423826451072581091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-9003390361863763623268591836600858000000000000)
      constant := (53050547336084541546794138608572068638288581028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9368876002923880919/6250000000000000000)
  centralHi := (29980403209356418941/20000000000000000000)
  directionLo := (158010598852980311433/100000000000000000000)
  directionHi := (79005299426490155717/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree011.table
  base := (5035092391802694352142938556875235455379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-1098784400599001745066781406248862625000000000)
      constant := (5839632123088244178068963687249496834834277874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree011.table
  base := (20095481984435437061044410415774384217593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-19800229786059594329148724222687933500000000000)
      constant := (105131421424210401681924440423025391939049858411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158010598852980311433/100000000000000000000)
  centralHi := (79005299426490155717/50000000000000000000)
  directionLo := (165722914181670149637/100000000000000000000)
  directionHi := (82861457090835074819/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree012.table
  base := (16458707399374719349386104535631028633357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-798872526696894008464656584415538000000000000)
      constant := (3960183841771687276284333147116878715850749157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree012.table
  base := (8209962774375909634438801005651774924987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-1199648824910647856208903598454119500000000000)
      constant := (5943429146997090818650680298377574490206288361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165722914181670149637/100000000000000000000)
  centralHi := (82861457090835074819/50000000000000000000)
  directionLo := (173091938633354486713/100000000000000000000)
  directionHi := (86545969316677243357/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree013.table
  base := (6690708143346111073178163487677284808863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-2559828756393846706759740329384125000000000)
      constant := (12176467907875754449654728566540201632638527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree013.table
  base := (6673906218712681842361176389988273306609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120994777572614282470930811905000000000000)
      linear := (-69192686126401563592815992075918250000000000)
      constant := (329046647632122689449129276301946710763296347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173091938633354486713/100000000000000000000)
  centralHi := (86545969316677243357/50000000000000000000)
  directionLo := (180159801717366190557/100000000000000000000)
  directionHi := (90079900858683095279/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree014.table
  base := (431240393580431970382351228531834285053/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-2794715137876039095914783634744391500000000000)
      constant := (13044232813825382057961473107428513675101743975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree014.table
  base := (268796950650988793075951744147960215649/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-12590288486527897788491672935573293000000000000)
      constant := (58766176699389226384212548803954766456687574460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180159801717366190557/100000000000000000000)
  centralHi := (90079900858683095279/50000000000000000000)
  directionLo := (93480330938958020031/50000000000000000000)
  directionHi := (186960661877916040063/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree015.table
  base := (8563348705931059337509613754366791492429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-997921305589572543725063525164426750000000000)
      constant := (4649062044811896836081903635860756737152145029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree015.table
  base := (4269057311935901835815720960298222284817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-499519000655330789992497896678385250000000000)
      constant := (2327751219282162472604185344370452854859924617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93480330938958020031/50000000000000000000)
  centralHi := (186960661877916040063/100000000000000000000)
  directionLo := (48380667642675334911/25000000000000000000)
  directionHi := (38704534114140267929/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree016.table
  base := (1664175300176708691664827066063901397003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-532135449276899361072599586040361500000000000)
      constant := (2506093294539810411724297805869519197586930406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree016.table
  base := (6634875696961185684760001579046885166149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-28767475097719929742206426970119021000000000000)
      constant := (135543461888901112228341424858026251679949942223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48380667642675334911/25000000000000000000)
  centralHi := (38704534114140267929/20000000000000000000)
  directionLo := (199869354729042792939/100000000000000000000)
  directionHi := (9993467736452139647/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree017.table
  base := (156413232585593456362460957118654053807/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-1695930737277037350848002228495528875000000000)
      constant := (8148688107896233327517273195702425474997431136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree017.table
  base := (1246594711570000266483861852727172833331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-15280462080025998412408983759802619250000000000)
      constant := (73466196240436820428888539729306764790646735474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199869354729042792939/100000000000000000000)
  centralHi := (9993467736452139647/5000000000000000000)
  directionLo := (51505153804493006623/25000000000000000000)
  directionHi := (206020615217972026493/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree018.table
  base := (3564819455216952846046308242006182152257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1196970084482251078985470465913315500000000000)
      constant := (5905936268942658894392682955709067909343928057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree018.table
  base := (110893041885251301827553804232062834431/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-599155059673778961248694593872064000000000000)
      constant := (2958500674581433452865334705822230203875453296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51505153804493006623/25000000000000000000)
  centralHi := (206020615217972026493/100000000000000000000)
  directionLo := (105996732060214282391/50000000000000000000)
  directionHi := (211993464120428564783/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree019.table
  base := (575086739211449054521674860836644274417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-631659838723238628702803056414805875000000000)
      constant := (3214738712512541618499997995729769493773058434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree019.table
  base := (2286371334367561245240272282232340179651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-34147822284716130990041048618577673500000000000)
      constant := (173938668775548629281069232074264990905076434377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105996732060214282391/50000000000000000000)
  centralHi := (211993464120428564783/100000000000000000000)
  directionLo := (217802579793645188887/100000000000000000000)
  directionHi := (27225322474205648611/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree020.table
  base := (1183630059665527084289284895882944127581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-3989007811232110307477225279237724000000000000)
      constant := (21001689762855751565496959951343270138849606943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree020.table
  base := (585811489977962822570615467645718887289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-17970635673524099036326294584031945500000000000)
      constant := (94701684813517285499705608396639897684548145003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217802579793645188887/100000000000000000000)
  centralHi := (27225322474205648611/12500000000000000000)
  directionLo := (111730365948289686319/50000000000000000000)
  directionHi := (223460731896579372639/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree021.table
  base := (191987322070412969682565861740593791079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1396018863374929614245877406662204250000000000)
      constant := (7617166013162166659894727974008985973953753679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree021.table
  base := (36337092301182610355059753117940849857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-4192746712153362795029347746394456500000000000)
      constant := (22899830387436308306494943273946748355020984855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/50000000000000000000)
  centralHi := (223460731896579372639/100000000000000000000)
  directionLo := (114489555893477323019/50000000000000000000)
  directionHi := (228979111786954646039/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree022.table
  base := (-692890676528945842429642269818069540207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1462368456339155792666013053578500500000000000)
      constant := (8277648821145718727114864361758674983785953993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree022.table
  base := (-701719064092947851291332771206960473887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-39528169471712332237875670267036326000000000000)
      constant := (223979860804023420911865579313843462595198764451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114489555893477323019/50000000000000000000)
  centralHi := (228979111786954646039/100000000000000000000)
  directionLo := (234367592831710456181/100000000000000000000)
  directionHi := (117183796415855228091/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree023.table
  base := (-297162865123557196253856491345326262837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (75036)
      previous := (37518)
      next := (37518)
      square := (363557285196291457146644531490000000000000)
      linear := (-8669478540472865620526363140802250000000000)
      constant := (50930175508159945653706946453579980736208205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree023.table
  base := (-746686159599146445697670490771406587311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1636007783383311557159900391705000000000000)
      linear := (-39056350221213988015583375062875750000000000)
      constant := (229689840319273293424812737774731149867099907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234367592831710456181/100000000000000000000)
  centralHi := (117183796415855228091/50000000000000000000)
  directionLo := (119817468994214450373/50000000000000000000)
  directionHi := (239634937988428900747/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree024.table
  base := (-2198782859996591393152804015121694486243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1595067642267608149506284347411093000000000000)
      constant := (9725209649951223664076472677364842391235389557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree024.table
  base := (-2205247694893420625983244649228041531361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1596854355421350607522175976518843000000000000)
      constant := (9746871946427834075784737893504400859054795239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119817468994214450373/50000000000000000000)
  centralHi := (239634937988428900747/100000000000000000000)
  directionLo := (122394483576370702977/50000000000000000000)
  directionHi := (48957793430548281191/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree025.table
  base := (-22732247776986873650858338563568759067/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1661417235231834327926419994327389250000000000)
      constant := (10510344635942341067268208010259427382268891625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree025.table
  base := (-2847056759413847931475532923777823564247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-44908516658708533485710291915494978500000000000)
      constant := (284417493245685314724814278928396488885634356731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122394483576370702977/50000000000000000000)
  centralHi := (48957793430548281191/20000000000000000000)
  directionLo := (124918346705651745587/50000000000000000000)
  directionHi := (9993467736452139647/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree026.table
  base := (-427745696049701297281109719929176877451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568999419730290475830103423545000000000000)
      linear := (-15335208534284560707217949478494250000000000)
      constant := (100609932135265080355645338467106413306941052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree026.table
  base := (-3426685875464007617704567416239398242893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-276342992432192902771135103343084000000000000)
      constant := (1815080868751270861202791266547273549896759281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124918346705651745587/50000000000000000000)
  centralHi := (9993467736452139647/4000000000000000000)
  directionLo := (12739221749157344381/5000000000000000000)
  directionHi := (254784434983146887621/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree027.table
  base := (-986629007305649708851232380210062493671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-897058210580143342383345644079990875000000000)
      constant := (6099879005403183159095014832812249792725387858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree027.table
  base := (-987636572343495347252636135400283908013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-898063236729123475017284685453100250000000000)
      constant := (6113770141368420377248479170131387296054459574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12739221749157344381/5000000000000000000)
  centralHi := (254784434983146887621/100000000000000000000)
  directionLo := (259637907950031730069/100000000000000000000)
  directionHi := (25963790795003173007/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree028.table
  base := (-4420415816356988309663130649477213137149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1860466014124512863186826935076278000000000000)
      constant := (13102993729927156565340151903361844793325742251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree028.table
  base := (-1105963886473258915712671389094159113437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-25144431922852367366772456781976815500000000000)
      constant := (177294830720042800850300610168133542879379413202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259637907950031730069/100000000000000000000)
  centralHi := (25963790795003173007/10000000000000000000)
  directionLo := (13220115182899967471/5000000000000000000)
  directionHi := (264402303657999349421/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree029.table
  base := (-4847929304574628654491679514576922622337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-5780446821266217124820887745977722750000000000)
      constant := (42134134815699238532309493334294778692233849589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree029.table
  base := (-4850864116767183668589206710065363557249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-52082312908036801816156454113439848500000000000)
      constant := (380076628334074215655425221477125205336946318077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/5000000000000000000)
  centralHi := (264402303657999349421/100000000000000000000)
  directionLo := (269082353777880875817/100000000000000000000)
  directionHi := (134541176888940437909/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree030.table
  base := (-1046506951516349256078024728272399462699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-1993165200052965220027098228908870500000000000)
      constant := (15024600676470534807153997241531316546926233505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree030.table
  base := (-5235038172515378605215378803174176488423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-5986195774485429877640888295880674000000000000)
      constant := (45177346842208365443603689337899355718275486131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269082353777880875817/100000000000000000000)
  centralHi := (134541176888940437909/50000000000000000000)
  directionLo := (273682385347746464597/100000000000000000000)
  directionHi := (136841192673873232299/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree031.table
  base := (-5577072106824774988209756389654505463567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2059514793017191398447233875825166750000000000)
      constant := (16042407050928279826262743815999563017989146633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree031.table
  base := (-5579207163141715364184550703175606248209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-55669211032700935981379535212412283500000000000)
      constant := (434141311374673787352068177637449457052954414157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273682385347746464597/100000000000000000000)
  centralHi := (136841192673873232299/50000000000000000000)
  directionLo := (139103183810274571861/50000000000000000000)
  directionHi := (278206367620549143723/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree032.table
  base := (-5883862432796419809513934577914576097899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-6377593157944252730602108568224389000000000000)
      constant := (51293769665067558736707825515727534946815194503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree032.table
  base := (-5885683112224391104324329313556892772833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-57462660095033003063991075761898501000000000000)
      constant := (462706616893532021821028776377167078188830838109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139103183810274571861/50000000000000000000)
  centralHi := (278206367620549143723/100000000000000000000)
  directionLo := (28265795216057141971/10000000000000000000)
  directionHi := (282657952160571419711/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree033.table
  base := (-6154804664819758114637107339650194936351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2192213978945643755287505169657759250000000000)
      constant := (18190979422572841625088321222275415008432784249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree033.table
  base := (-6156357143302766641449092841766094236739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2194670709532039635059356159680915500000000000)
      constant := (18232869381162605470346675079811012627891296661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28265795216057141971/10000000000000000000)
  centralHi := (282657952160571419711/100000000000000000000)
  directionLo := (287040507341029530181/100000000000000000000)
  directionHi := (143520253670514765091/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree034.table
  base := (-6391453919096252422421964449328176620099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2258563571909869933707640816574055500000000000)
      constant := (19321436624635719014172826658571165400736529301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree034.table
  base := (-6392777659836212220591017419405186980171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-61049558219697137229214156860870936000000000000)
      constant := (522880142990171643686607247355423841602214775583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287040507341029530181/100000000000000000000)
  centralHi := (143520253670514765091/50000000000000000000)
  directionLo := (291357148169704897491/100000000000000000000)
  directionHi := (72839287042426224373/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree035.table
  base := (-824385627784708315590884659002955063837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-3487369747311144168191664695235527625000000000)
      constant := (30733771285650486117100265013281023119711150356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree035.table
  base := (-3298106863214232417228846676457275814171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-31421503641014602155912848705178576750000000000)
      constant := (277240781343735332564436726196061257746432057583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291357148169704897491/100000000000000000000)
  centralHi := (72839287042426224373/25000000000000000000)
  directionLo := (2956107621934139261/1000000000000000000)
  directionHi := (295610762193413926101/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree036.table
  base := (-67667440711841621879361147995067497249/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1195631378919161145273956055203324000000000000)
      constant := (10847059298932418767346952440795360346422107550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree036.table
  base := (-6767706501648518043648106802989754806321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2393942827568935977571749554068273000000000000)
      constant := (21744045155800825703954032344358520930560096279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2956107621934139261/1000000000000000000)
  centralHi := (295610762193413926101/100000000000000000000)
  directionLo := (299804032093564189409/100000000000000000000)
  directionHi := (29980403209356418941/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree037.table
  base := (-6907290321907619374325847677597233702123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2457612350802548468968047757322944250000000000)
      constant := (22936173028575389223546505704274351608234001677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree037.table
  base := (-6908111014926133644625969556485655153269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-66429905406693338477048778509329588500000000000)
      constant := (620701048654503176692390898040767987634600149537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299804032093564189409/100000000000000000000)
  centralHi := (29980403209356418941/10000000000000000000)
  directionLo := (303939455475176195117/100000000000000000000)
  directionHi := (151969727737588097559/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree038.table
  base := (-3508715127445184245759765784892409430471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-3785942915650161971082275106358860750000000000)
      constant := (36322921483760931545779078695999894691644386387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree038.table
  base := (-7018130133071512489742988590052843366857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-68223354469025405559660319058815806000000000000)
      constant := (655315354432229446492939962825058717629309668261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303939455475176195117/100000000000000000000)
  centralHi := (151969727737588097559/50000000000000000000)
  directionLo := (154009681132010625839/50000000000000000000)
  directionHi := (308019362264021251679/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree039.table
  base := (-88721816302881178362979921621891216987/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-7663643599795860431385559322945375000000000)
      constant := (75536658280682633380794727583020856067305080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree039.table
  base := (-7098342203486593450466284749203223827813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137998839460580951660206847090000000000000)
      linear := (-46033401401286964261848691392703500000000000)
      constant := (454260841886408233733142144471658640035260769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154009681132010625839/50000000000000000000)
  centralHi := (308019362264021251679/100000000000000000000)
  directionLo := (312045930056012916673/100000000000000000000)
  directionHi := (156022965028006458337/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree040.table
  base := (-3574357225845676276323781218289571843867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1328330564847613502114227349035916500000000000)
      constant := (13442229368108545302073476924089728987586446333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree040.table
  base := (-223413236666061993827816724269417699721/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-35905126296844769862441700078894120500000000000)
      constant := (363773028532950704722715662438637671014168923728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312045930056012916673/100000000000000000000)
  centralHi := (156022965028006458337/50000000000000000000)
  directionLo := (316021197705960622867/100000000000000000000)
  directionHi := (79005299426490155717/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree041.table
  base := (-7170732654586328301927899857922197403077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-8169032167978359547945771034964387750000000000)
      constant := (84823351174902785998188714742114204272715039369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree041.table
  base := (-7171166952478693533457655267517637945731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-73603701656021606807494940707274458500000000000)
      constant := (765160356168432747221463713927631914956619977463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316021197705960622867/100000000000000000000)
  centralHi := (79005299426490155717/25000000000000000000)
  directionLo := (39993384674549926967/12500000000000000000)
  directionHi := (319947077396399415737/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree042.table
  base := (-3582062945318990118440460267525748985983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1394680157811839680534362995952212750000000000)
      constant := (14850668161193934898164807859566353749279133817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree042.table
  base := (-7164496402562398451622445982459797155697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2792487063642728662596536342842988000000000000)
      constant := (29769365021786126854259148298022893299483532503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39993384674549926967/12500000000000000000)
  centralHi := (319947077396399415737/100000000000000000000)
  directionLo := (40478170673657035999/12500000000000000000)
  directionHi := (323825365389256287993/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree043.table
  base := (-7129163453108597832958943375851931771347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2855709908587905539488861638820721750000000000)
      constant := (31165092453390972053552173500779559471147306853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree043.table
  base := (-7129479583728319971728389385392610736179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-77190599780685740972718021806246893500000000000)
      constant := (843382909239950634718144214623468350010771252967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40478170673657035999/12500000000000000000)
  centralHi := (323825365389256287993/100000000000000000000)
  directionLo := (65531550326380373379/20000000000000000000)
  directionHi := (20478609476993866681/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree044.table
  base := (-3533034004401008788347443383091708479909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-4383089252328197576863495928605527000000000000)
      constant := (48998548317012958477997073233546542198062966473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree044.table
  base := (-7066337771310478380608226274229783498013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-78984048843017808055329562355733111000000000000)
      constant := (883989983003232683994000731436176963388341774249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65531550326380373379/20000000000000000000)
  centralHi := (20478609476993866681/6250000000000000000)
  directionLo := (165722914181670149637/50000000000000000000)
  directionHi := (13257833134533611971/4000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree045.table
  base := (-6975023834212381720413452945499548683009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2988409094516357896329132932653314250000000000)
      constant := (34203139121738017780167160978977722621627812391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree045.table
  base := (-6975254056454114611109240740128464307837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-2991759181679625005108929737230345500000000000)
      constant := (34281245738063767755827947898845865631165064363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165722914181670149637/50000000000000000000)
  centralHi := (13257833134533611971/4000000000000000000)
  directionLo := (335191097844869058957/100000000000000000000)
  directionHi := (167595548922434529479/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree046.table
  base := (-3428091783277481228689029249136133073303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (60592880866048576191107421915000000000000)
      linear := (-2887295545822858293713864441937250000000000)
      constant := (33816067616880364734130025769897227885611793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree046.table
  base := (-6856380066749754071246364848076560029199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45630000000000000000000000000000000000000000
      center := (675324)
      previous := (337662)
      next := (337662)
      square := (3272015566766623114319800783410000000000000)
      linear := (-156088746630778718753407643581674000000000000)
      constant := (1830233457487043130026754897353155031586764963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335191097844869058957/100000000000000000000)
  centralHi := (167595548922434529479/50000000000000000000)
  directionLo := (10590468103802242481/3125000000000000000)
  directionHi := (338894979321671759393/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree047.table
  base := (-3354836871489945963771246515614094734559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-4681662420667215379754106339728860125000000000)
      constant := (56082703224337656521271888401681042516313322523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree047.table
  base := (-6709841479461007434656579684315565952459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-84364396030014009303164184004191763500000000000)
      constant := (1011789271888832753562883840584659832539923749407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10590468103802242481/3125000000000000000)
  centralHi := (338894979321671759393/100000000000000000000)
  directionLo := (34255881530683760187/10000000000000000000)
  directionHi := (342558815306837601871/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree048.table
  base := (-1633899837498278605948753182338477495513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1593728936704518215794769936701101500000000000)
      constant := (19518168784268217615426866498746010046847284574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree048.table
  base := (-6535742548755258587350837436565675643711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-9573093899149564042863969394853109000000000000)
      constant := (117375633545639827666680881581881418095329778667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34255881530683760187/10000000000000000000)
  centralHi := (342558815306837601871/100000000000000000000)
  directionLo := (173091938633354486713/50000000000000000000)
  directionHi := (346183877266708973427/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree049.table
  base := (-3167023781812194732460716537746872412201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1626903733186631305004837760159249625000000000)
      constant := (20360499000984591003994009381841738777445568399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree049.table
  base := (-6334169826940131581453095882453991843221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-87951294154678143468387265103164198500000000000)
      constant := (1101967580154125846853019405026141506137303383233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173091938633354486713/50000000000000000000)
  centralHi := (346183877266708973427/100000000000000000000)
  directionLo := (87442842693956221911/25000000000000000000)
  directionHi := (69954274155164977529/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree050.table
  base := (-6105090827290350743921951573962991725527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-9960471178012466365289433501704386500000000000)
      constant := (127327330920028362630388616727835326386488482019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree050.table
  base := (-610519522618731591287867154507682672069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-44872371608505105275499402826325208000000000000)
      constant := (574274866517696647190350736107645030231138509685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87442842693956221911/25000000000000000000)
  centralHi := (69954274155164977529/20000000000000000000)
  directionLo := (176661220100357137319/50000000000000000000)
  directionHi := (353322440200714274639/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree051.table
  base := (-2924394693537747231478683494293748045007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1693253326150857483424973407075545875000000000)
      constant := (22100334548298525896154457931996059705247079193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree051.table
  base := (-5848878540063056943352752709669433357787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3390303417753417690133716526005060500000000000)
      constant := (44301000600860598601496929990421995207130484413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176661220100357137319/50000000000000000000)
  centralHi := (353322440200714274639/100000000000000000000)
  directionLo := (178419086482062689693/50000000000000000000)
  directionHi := (356838172964125379387/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree052.table
  base := (-17391229318964735999288336338354297309/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-10215551021496867293698468819726000000000000)
      constant := (136081863577654699591044040498284004775766240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree052.table
  base := (-5565269522154910902414557509360815867313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-552258232790972453942141341725579000000000000)
      constant := (7365084672314209824504652990034417466967168421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178419086482062689693/50000000000000000000)
  centralHi := (356838172964125379387/100000000000000000000)
  directionLo := (72063920686946476223/20000000000000000000)
  directionHi := (90079900858683095279/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree053.table
  base := (-5254344569460632979768707183397884297861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-10557617514690501971070654323951052750000000000)
      constant := (143482326854476697050366318141765943182973286217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree053.table
  base := (-1050881920240145153386364030686573964591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-95125090404006411798833427301109068500000000000)
      constant := (1294266513227183195314850496675369814290116001215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72063920686946476223/20000000000000000000)
  centralHi := (90079900858683095279/25000000000000000000)
  directionLo := (181883858240877544777/50000000000000000000)
  directionHi := (72753543296351017911/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree054.table
  base := (-2458138874766406858107365895857140621497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1792777715597196751055176877449990250000000000)
      constant := (24847991586075955548659770173868401380672546703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree054.table
  base := (-983266659518838562446285805467519608927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3589575535790314032646109920392418000000000000)
      constant := (49808464582045297204854113215157896522211586365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181883858240877544777/50000000000000000000)
  centralHi := (72753543296351017911/20000000000000000000)
  directionLo := (91795862682278027233/25000000000000000000)
  directionHi := (367183450729112108933/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree055.table
  base := (-4551021943813879045636259073037624220683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3651905024158619680530489401816276750000000000)
      constant := (51601289956672644429046455028735372692984219117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree055.table
  base := (-284441837145131172271785913929033753981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-49355994264335272982028254200040751750000000000)
      constant := (698192665804035150783341652979135929253959437704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91795862682278027233/25000000000000000000)
  centralHi := (367183450729112108933/100000000000000000000)
  directionLo := (370567701539578386947/100000000000000000000)
  directionHi := (92641925384894596737/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree056.table
  base := (-2079300685011565332335620548762318398883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-5577381925684268788425937573098859500000000000)
      constant := (80315040709949163581482580805840414418464382751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree056.table
  base := (-4158641905765973101830509596747890588511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-100505437591002613046668048949567721000000000000)
      constant := (1448936818939162502207172116883749040504406258403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370567701539578386947/100000000000000000000)
  centralHi := (92641925384894596737/25000000000000000000)
  directionLo := (93480330938958020031/25000000000000000000)
  directionHi := (2991370590046656641/800000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree057.table
  base := (-747807249910636770175226858040373938971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3784604210087072037370760695648869250000000000)
      constant := (55522192914219583774716512112357714858347768145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree057.table
  base := (-3739070879959177777671032888666318505951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-11366542961481631125475509944339326500000000000)
      constant := (166942550812890600058616686096947445533998423947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93480330938958020031/25000000000000000000)
  centralHi := (2991370590046656641/800000000000000000)
  directionLo := (377245134222167985001/100000000000000000000)
  directionHi := (188622567111083992501/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree058.table
  base := (-3292343476822718873795958816217376625167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3850953803051298215790896342565165500000000000)
      constant := (57537785769055144155453235406343287281083445033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree058.table
  base := (-658474612698748192692348357109459075677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-104092335715666747211891130048540156000000000000)
      constant := (1557023706315253000923158433420293488513679070605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377245134222167985001/100000000000000000000)
  centralHi := (188622567111083992501/50000000000000000000)
  directionLo := (95134978526988591029/25000000000000000000)
  directionHi := (380539914107954364117/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree059.table
  base := (-176158573411682985857587404177352190727/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-5875955094023286591316547984222192625000000000)
      constant := (89385206662826529909406794496340968793279821352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree059.table
  base := (-2818562453047962258162194487192497979269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-105885784777998814294502670598026373500000000000)
      constant := (1612559032151315313507939139036295794586445047537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95134978526988591029/25000000000000000000)
  centralHi := (380539914107954364117/100000000000000000000)
  directionLo := (383806411051557385493/100000000000000000000)
  directionHi := (191903205525778692747/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree060.table
  base := (-463525831001312414242592936728930321641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-3983652988979750572631167636397758000000000000)
      constant := (61679247876688227780480764602620917626574864795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree060.table
  base := (-1158825376618239016766755676568383267253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-1994059885932053358835448354583566500000000000)
      constant := (30909053825394213044676912256415537467524314547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383806411051557385493/100000000000000000000)
  centralHi := (191903205525778692747/50000000000000000000)
  directionLo := (387045341141402679289/100000000000000000000)
  directionHi := (38704534114140267929/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree061.table
  base := (-13981478927879411491364758354297013959/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2025001290971988375525651641657027125000000000)
      constant := (31902557594882935147732823586105041791642042224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree061.table
  base := (-223705969623919870089038101223856153719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-54736341451331474229862875848499404250000000000)
      constant := (863306652968362866142551563043658698716272709548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387045341141402679289/100000000000000000000)
  centralHi := (38704534114140267929/10000000000000000000)
  directionLo := (195128695374522326917/50000000000000000000)
  directionHi := (78051478149808930767/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree062.table
  base := (-246909178735550841546640662472303264171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-12349056524724608788414316790691051500000000000)
      constant := (197903216923756162681323576600258398644447726435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree062.table
  base := (-1234561661821925539733667466130821502173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-111266131964995015542337292246485026000000000000)
      constant := (1785132210460260666550950524271884023900874253929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195128695374522326917/50000000000000000000)
  centralHi := (78051478149808930767/20000000000000000000)
  directionLo := (393443218227535687243/100000000000000000000)
  directionHi := (98360804556883921811/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree063.table
  base := (-652385859782841709999473560454221508033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4182701767872429107891574577146646750000000000)
      constant := (68167118611414692760768947041671826103897841767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree063.table
  base := (-652399332955539103487910024200214536129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4187391889901003060183290103554490500000000000)
      constant := (68320207539645227455037364310709528589005531271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393443218227535687243/100000000000000000000)
  centralHi := (98360804556883921811/25000000000000000000)
  directionLo := (39660345548699902413/10000000000000000000)
  directionHi := (396603455486999024131/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree064.table
  base := (-43155010166141709351172998381502664439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4249051360836655286311710224062943000000000000)
      constant := (70403253580916017895004184056577027280296488961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree064.table
  base := (-43166522436867258100976862281619451323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-114853030089659149707560373345457461000000000000)
      constant := (1905153471382766432616585892498340409364671356879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39660345548699902413/10000000000000000000)
  centralHi := (396603455486999024131/100000000000000000000)
  directionLo := (399738709458085585879/100000000000000000000)
  directionHi := (9993467736452139647/2500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree065.table
  base := (296570892531277192867018785380702474359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568999419730290475830103423545000000000000)
      linear := (-38302375329593622468034134949519875000000000)
      constant := (645054527642278202675481584834416147483057733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree065.table
  base := (118626389663596158605635085641330561617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-690215852970362229527644460916826500000000000)
      constant := (11637016581415574898890939641462958278307878055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399738709458085585879/100000000000000000000)
  centralHi := (9993467736452139647/2500000000000000000)
  directionLo := (201424781726457078047/50000000000000000000)
  directionHi := (80569912690582831219/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree066.table
  base := (628250220667090277177212806481193460833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2190875273382553821575990758947767750000000000)
      constant := (37492893923296056254367267377850092535966931033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree066.table
  base := (1256492036316136375240984883202480111397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-13159992023813698208087050493825544000000000000)
      constant := (225461398493414774439956944940647745648317009591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201424781726457078047/50000000000000000000)
  centralHi := (80569912690582831219/20000000000000000000)
  directionLo := (5074207230401723909/1250000000000000000)
  directionHi := (405936578432137912721/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree067.table
  base := (194691753159258995211904248577602289839/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2224050069864666910786058582405915875000000000)
      constant := (38666093235610038166429808725030830810788232195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree067.table
  base := (1946910350005208611740922649478587842877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-120233377276655350955394994993916113500000000000)
      constant := (2092643815740648135744751872821910662163258260279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5074207230401723909/1250000000000000000)
  centralHi := (405936578432137912721/100000000000000000000)
  directionLo := (409000294185932097973/100000000000000000000)
  directionHi := (204500147092966048987/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree068.table
  base := (2664390179399002844826198657114410157091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-13543349198080679999976758435184384000000000000)
      constant := (239146017193272196880386424185711375022362277473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree068.table
  base := (2664384043268380922787867793930492211791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-122026826338987418038006535543402331000000000000)
      constant := (2157129483288944038253762547583890006224110834157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409000294185932097973/100000000000000000000)
  centralHi := (204500147092966048987/50000000000000000000)
  directionLo := (82408246087188810597/20000000000000000000)
  directionHi := (206020615217972026493/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree069.table
  base := (1704457984814001604631201658869234095543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (60592880866048576191107421915000000000000)
      linear := (-4329678001566905650673335027074125000000000)
      constant := (77632557098572261883412851889782412280896767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree069.table
  base := (3408910726879643013781229262089397867343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (121185761732097152382214843830000000000000)
      linear := (-8669066400708498573172168038429500000000000)
      constant := (155612237157350866396083432601591576989580967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82408246087188810597/20000000000000000000)
  centralHi := (206020615217972026493/50000000000000000000)
  directionLo := (207529943932288054579/50000000000000000000)
  directionHi := (415059887864576109159/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree070.table
  base := (4180492873817874065262060195647040076639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4647148918622012356832524105560720500000000000)
      constant := (84591905327469732710681800690206487748641603239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree070.table
  base := (261280524656342677500167496107040306529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-62806862231825776101614808321187383000000000000)
      constant := (1144542055493095818751438464113909727443403811864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207529943932288054579/50000000000000000000)
  centralHi := (415059887864576109159/100000000000000000000)
  directionLo := (418056749077373753117/100000000000000000000)
  directionHi := (209028374538686876559/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree071.table
  base := (2489559593868363911849506666555819795099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-7070247767379357802878989628715525125000000000)
      constant := (130627977995407304337799526148365490915411187097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree071.table
  base := (1244778840200775527999267747994321325753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-63703586762991809642920578595930491750000000000)
      constant := (1178276531112047345856986837594859839153681773462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418056749077373753117/100000000000000000000)
  centralHi := (209028374538686876559/50000000000000000000)
  directionLo := (84206455900751454597/20000000000000000000)
  directionHi := (210516139751878636493/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree072.table
  base := (1160958695827660971334168129095314129307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4779848104550464713672795399393313000000000000)
      constant := (89615485290650615759210343088711006892370875535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree072.table
  base := (5804790209687150304934261262071854608587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4785208244011692087720470286716563000000000000)
      constant := (89815423467182872890490768280801016873862286387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84206455900751454597/20000000000000000000)
  centralHi := (210516139751878636493/50000000000000000000)
  directionLo := (84797385648171425913/20000000000000000000)
  directionHi := (211993464120428564783/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree073.table
  base := (3328757272011349702250260575554450379109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2423098848757345446046465523154804625000000000)
      constant := (46091202550484087868946446153414780398811473709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree073.table
  base := (6657511750952247340651693933211050268093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-130994071650647753451064238290833418500000000000)
      constant := (2494474222282780039820777243374980024241730121911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84797385648171425913/20000000000000000000)
  centralHi := (211993464120428564783/50000000000000000000)
  directionLo := (426921128844784958193/100000000000000000000)
  directionHi := (213460564422392479097/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree074.table
  base := (3768640685000052032592112013020942654399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-7368820935718375605769600039838858250000000000)
      constant := (142179117006073332484551180910658807085862774997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree074.table
  base := (7537278983999604595679903734765733115943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-132787520712979820533675778840319636000000000000)
      constant := (2564926425815349734899929745623970461145057343861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426921128844784958193/100000000000000000000)
  centralHi := (213460564422392479097/50000000000000000000)
  directionLo := (429835300073287635447/100000000000000000000)
  directionHi := (53729412509160954431/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree075.table
  base := (8444093105590182530051666332915801531977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-4978896883443143248933202340142201750000000000)
      constant := (97426503923769559968302596024657042096197775777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree075.table
  base := (8444091067425049521036638171513579436781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-14953441086145765290698591043311761500000000000)
      constant := (292930338020071393741035118526090416701932974543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429835300073287635447/100000000000000000000)
  centralHi := (53729412509160954431/12500000000000000000)
  directionLo := (216364923291693108391/50000000000000000000)
  directionHi := (432729846583386216783/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree076.table
  base := (468897451724214863244826171651194982079/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2522623238203684713676668993529249000000000000)
      constant := (50051841398045741084751369465229025388428446790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree076.table
  base := (1875589458706216474304795311175999672867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-136374418837643954698898859939292071000000000000)
      constant := (2708814069670399133411484345407983779811787660045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216364923291693108391/50000000000000000000)
  centralHi := (432729846583386216783/100000000000000000000)
  directionLo := (17424206383491615111/4000000000000000000)
  directionHi := (27225322474205648611/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree077.table
  base := (10338848553959452098677132234997197257691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-15334788208114786817320420901924382750000000000)
      constant := (308452843701391849037841760807432257116416999273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree077.table
  base := (5169423533477063626107026555735430895791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-69083933949988010890755200244389144250000000000)
      constant := (1391124753423757414907354268090022220281019502157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17424206383491615111/4000000000000000000)
  centralHi := (27225322474205648611/6250000000000000000)
  directionLo := (219230808734799215729/50000000000000000000)
  directionHi := (438461617469598431459/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree078.table
  base := (11326791156767153179101345475035299140171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379332946486860317220068949030000000000000)
      linear := (-30638731729797762036648575626574500000000000)
      constant := (624664492257623904726315797533633891995150459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree078.table
  base := (1769810919802429451133368680743851191/1562500000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-15336545799069481576169399631631000000000000)
      constant := (313026446691076282292510483835385253796124800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219230808734799215729/50000000000000000000)
  centralHi := (438461617469598431459/100000000000000000000)
  directionLo := (441299586368539677909/100000000000000000000)
  directionHi := (44129958636853967791/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree079.table
  base := (12341776415932136830571458491846488148413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5244295255300047962613744927807386750000000000)
      constant := (108355736631142937280040977078154036097893770613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree079.table
  base := (2468355066255190720994435841596542149597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-141754766024640155946733481587750723500000000000)
      constant := (2932103605618473103839996217803201546892926388595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441299586368539677909/100000000000000000000)
  centralHi := (44129958636853967791/10000000000000000000)
  directionLo := (444119420723786809947/100000000000000000000)
  directionHi := (111029855180946702487/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree080.table
  base := (13383803971988928414709738926587799660511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-15931934544792822423101641724171049000000000000)
      constant := (333539780561422606775047403510322672632348031733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree080.table
  base := (13383803045704643780003799564757878234513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-143548215086972223029345022137236941000000000000)
      constant := (3008522265338051210396808155906018844945179811251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444119420723786809947/100000000000000000000)
  centralHi := (111029855180946702487/25000000000000000000)
  directionLo := (111730365948289686319/25000000000000000000)
  directionHi := (446921463793158745277/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree081.table
  base := (14452873522261675984135813509266219795207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5376994441228500319454016221639979250000000000)
      constant := (114040869832472710993724089308334046651848801007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree081.table
  base := (14452872731272977091053285446489078373479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5383024598122381115257650469878635500000000000)
      constant := (114293901145939590140330830278614912314417396079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730365948289686319/25000000000000000000)
  centralHi := (446921463793158745277/100000000000000000000)
  directionLo := (224853024070173142057/50000000000000000000)
  directionHi := (89941209628069256823/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree082.table
  base := (1943623101482160623023478235164949247269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2721672017096363248937075934278137750000000000)
      constant := (58469282772175382969942258436260844119995383476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree082.table
  base := (15548984136444502894288812319639516547689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-147135113211636357194568103236209376000000000000)
      constant := (3164342801818260797968120361134639389184758495803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224853024070173142057/50000000000000000000)
  centralHi := (89941209628069256823/20000000000000000000)
  directionLo := (226236748047811187079/50000000000000000000)
  directionHi := (452473496095622374159/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree083.table
  base := (16672137626095747565196896416109068147673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-16529080881470858028882862546417715250000000000)
      constant := (359619041910747279145186509065508026349722841619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree083.table
  base := (4168034262352044040751704811530745664811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-74464281136984212138589821892847796750000000000)
      constant := (1621872338730225791775349605176815646384832483394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226236748047811187079/50000000000000000000)
  centralHi := (452473496095622374159/100000000000000000000)
  directionLo := (455224120191343707937/100000000000000000000)
  directionHi := (227612060095671853969/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree084.table
  base := (8911165892073259155083414812327712413559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2788021610060589427357211581194434000000000000)
      constant := (61422107547000630364216085441683388629984588159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree084.table
  base := (4455582822946390991963033085422733240509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-8373445074238916186655065796398989500000000000)
      constant := (184674497635353700717450130770449129646608470654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455224120191343707937/100000000000000000000)
  centralHi := (227612060095671853969/50000000000000000000)
  directionLo := (114489555893477323019/25000000000000000000)
  directionHi := (457958223573909292077/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree085.table
  base := (18999567133677333543874886066558161964073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5642392813085405033134558809305164250000000000)
      constant := (125852168901988612275165932328402748386187590273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree085.table
  base := (18999566713340199284354031612208039056073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-152515460398632558442402724884668028500000000000)
      constant := (3405531641383361045570052707046714814446853521371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114489555893477323019/25000000000000000000)
  centralHi := (457958223573909292077/100000000000000000000)
  directionLo := (92135220078742620811/20000000000000000000)
  directionHi := (57584512549214138007/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree086.table
  base := (10101921773176622184886373927708693781737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-8563113609074446817332041684332190750000000000)
      constant := (193345313074106812383444706784372828126468208611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree086.table
  base := (10101921593764176325873782885233664058743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-77154454730482312762507132717077123000000000000)
      constant := (1743958364497990105332730194909388894801423439461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92135220078742620811/20000000000000000000)
  centralHi := (57584512549214138007/12500000000000000000)
  directionLo := (463378036174510736851/100000000000000000000)
  directionHi := (115844509043627684213/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree087.table
  base := (21435160914049863535726613358394708172171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5775091999013857389974830103137756750000000000)
      constant := (131978334526582620325095773467126803141237759571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree087.table
  base := (1339697537984781409327246153947251757049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2890784417098086900141218629326675250000000000)
      constant := (66135115185498625702376759882095284269030501192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463378036174510736851/100000000000000000000)
  centralHi := (115844509043627684213/25000000000000000000)
  directionLo := (466064308163512910863/100000000000000000000)
  directionHi := (29129019260219556929/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree088.table
  base := (1134675957283338399510310241627605616373/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2920720795989041784197482875027026500000000000)
      constant := (67548273162689189781166990400270550197093625730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree088.table
  base := (22693518884232539867539116556127084600611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-157895807585628759690237346533126681000000000000)
      constant := (3655670114229455160003780543949718715240239048297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466064308163512910863/100000000000000000000)
  centralHi := (29129019260219556929/6250000000000000000)
  directionLo := (468735185663420912363/100000000000000000000)
  directionHi := (117183796415855228091/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree089.table
  base := (5994729541111340751538620001961189227609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-8861686777413464620222652095455523875000000000)
      constant := (207377266158394286260226199830760747235231083254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree089.table
  base := (239789179413159461707554992568906893243/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-79844628323980413386424443541306449250000000000)
      constant := (1870519205725492600598594933716182293672928548050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468735185663420912363/100000000000000000000)
  centralHi := (117183796415855228091/25000000000000000000)
  directionLo := (3682741643340074313/781250000000000000)
  directionHi := (94278186069505902413/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree090.table
  base := (252913579057108909181530620213308184123/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-2987070388953267962617618521943322750000000000)
      constant := (70721613930727033074250081208550567232814016150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree090.table
  base := (25291357715287426374582979435407988837947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-5980840952233070142794830653040708000000000000)
      constant := (141755596723248465059745085249396395235101299747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3682741643340074313/781250000000000000)
  centralHi := (94278186069505902413/20000000000000000000)
  directionLo := (4740317965589409343/1000000000000000000)
  directionHi := (474031796558940934301/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree091.table
  base := (13315419157485574830952028088681631705909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-17871273286599887880637197310067875000000000)
      constant := (428022773929231799203052580788868251141175861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree091.table
  base := (13315419076235621179177165302834127203167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120994777572614282470930811905000000000000)
      linear := (-483065546664570890349325349649660750000000000)
      constant := (11582124894467636924056115495700251916967834261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4740317965589409343/1000000000000000000)
  centralHi := (474031796558940934301/100000000000000000000)
  directionLo := (14895563487339321191/3125000000000000000)
  directionHi := (476658031594858278113/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree092.table
  base := (27997359346315283070839590521473911980057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (75036)
      previous := (37518)
      next := (37518)
      square := (363557285196291457146644531490000000000000)
      linear := (-34632362743865718045796833673266000000000000)
      constant := (838961738835749869571256872789308648373888899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree092.table
  base := (699933980191354789306176638037324241217/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1636007783383311557159900391705000000000000)
      linear := (-156020419503740102098944715246759500000000000)
      constant := (3783657580102936222381388194659102710253463420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14895563487339321191/3125000000000000000)
  centralHi := (476658031594858278113/100000000000000000000)
  directionLo := (479269875976857801493/100000000000000000000)
  directionHi := (239634937988428900747/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree093.table
  base := (14695460480532528853798869622498276021619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3086594778399607230247821992317767125000000000)
      constant := (75619447468933415006133068836756217386327510219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree093.table
  base := (29390920842754142818495317467480354861409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-18540339210809899455921672142284196500000000000)
      constant := (454717291965813400995114747798400122021144478027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479269875976857801493/100000000000000000000)
  centralHi := (239634937988428900747/50000000000000000000)
  directionLo := (481867563707976099621/100000000000000000000)
  directionHi := (240933781853988049811/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree094.table
  base := (962860097707457332987197633614979090727/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3119769574881720319457889815775915250000000000)
      constant := (77288811277328154091626699956896555165416352432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree094.table
  base := (6162304605139712540996110878579751208171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-168656501959621162185906589830043986000000000000)
      constant := (4182795938082885990300241798391075003972828902085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481867563707976099621/100000000000000000000)
  centralHi := (240933781853988049811/50000000000000000000)
  directionLo := (484451322517389925811/100000000000000000000)
  directionHi := (121112830629347481453/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree095.table
  base := (32259165815593216823162752685620515701487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-18917666228183000452007745835404380250000000000)
      constant := (473859308387856744033707209081028326555498417861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree095.table
  base := (1008098929046243019554944568682692788197/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-85224975510976614634259065189765101750000000000)
      constant := (2137065325427705406570546299515878115135808198704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484451322517389925811/100000000000000000000)
  centralHi := (121112830629347481453/25000000000000000000)
  directionLo := (121755343523353190051/25000000000000000000)
  directionHi := (97404274818682552041/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree096.table
  base := (3373384900481830137783227858378653066289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3186119167845946497878025462692211500000000000)
      constant := (80682667829844273716243178523878568813896514445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree096.table
  base := (33733848931359004423443942983404846874941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-6379385188306862827819617441815423000000000000)
      constant := (161720732072407688740282460829300364715466600341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121755343523353190051/25000000000000000000)
  centralHi := (97404274818682552041/20000000000000000000)
  directionLo := (489577934305482811909/100000000000000000000)
  directionHi := (48957793430548281191/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree097.table
  base := (281884581398846070025288443557661367749/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-6438587928656119174176186572300719250000000000)
      constant := (164814321144125630205636152058812679578203543625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree097.table
  base := (8808893153048914408661276126339223737499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-87018424573308681716870605739251319250000000000)
      constant := (2229891641667737134805508879199718054286356997346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489577934305482811909/100000000000000000000)
  centralHi := (48957793430548281191/10000000000000000000)
  directionLo := (98424242683154314477/20000000000000000000)
  directionHi := (246060606707885786193/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree098.table
  base := (36764336809326732887226234132154181484591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-19514812564861036057788966657651046500000000000)
      constant := (504900177743397630659679470273643975092961759973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree098.table
  base := (36764336755882119917653518451872713951657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-175830298208949430516352752027988856000000000000)
      constant := (4554101202957929834780010086333248307374786361339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98424242683154314477/20000000000000000000)
  centralHi := (246060606707885786193/50000000000000000000)
  directionLo := (494651416280999984493/100000000000000000000)
  directionHi := (247325708140499992247/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree099.table
  base := (38320141394448527920509593406791712132109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-6571287114584571531016457866133311750000000000)
      constant := (171822549969477100682720582647945343754760176709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree099.table
  base := (4790017668608421239154307011181527688763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3289328653171879585166005418101390250000000000)
      constant := (86100250459067860560372332196999039636987403852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494651416280999984493/100000000000000000000)
  centralHi := (247325708140499992247/50000000000000000000)
  directionLo := (497168742545010448911/100000000000000000000)
  directionHi := (31073046409063153057/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree100.table
  base := (39902986418627311550421286521692269167779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-6637636707548797709436593513049608000000000000)
      constant := (175381793308122801392434594839982626180868610379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree100.table
  base := (623484162183678791010180353331723850207/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-89708598166806782340787916563480645500000000000)
      constant := (2372860124401585144025564070963716259557555590048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497168742545010448911/100000000000000000000)
  centralHi := (31073046409063153057/6250000000000000000)
  directionLo := (499673386822606982349/100000000000000000000)
  directionHi := (9993467736452139647/2000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree101.table
  base := (41512871872114705869263193946286777640383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-20111958901539071663570187479897712750000000000)
      constant := (536933367788594392847127221249522299318796141749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree101.table
  base := (41512871838966941984019693872613823346013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-181210645395945631764187373676447508500000000000)
      constant := (4843021374975324283280721847181727498522086521751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499673386822606982349/100000000000000000000)
  centralHi := (9993467736452139647/2000000000000000000)
  directionLo := (502165538875142621433/100000000000000000000)
  directionHi := (251082769437571310717/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree102.table
  base := (2157489887335911043700986680530950947403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3385167946738625033138432403441100250000000000)
      constant := (91305268916485336276892211662441804315862756030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree102.table
  base := (5393724714806710134399007535305893487277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-10166894136570983269266606345885207000000000000)
      constant := (274517605738149973614980280717069209891372612924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502165538875142621433/100000000000000000000)
  centralHi := (251082769437571310717/50000000000000000000)
  directionLo := (63080672972287800819/12500000000000000000)
  directionHi := (504645383778302406553/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree103.table
  base := (22406882017778535489868276923476598828157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3418342743220738122348500226899248375000000000)
      constant := (93140019508912638547290069785831952454804813957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree103.table
  base := (44813764011458094050426427686445106809897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-184797543520609765929410454775419943500000000000)
      constant := (5040606833720984418520339713533763938491863245819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63080672972287800819/12500000000000000000)
  centralHi := (504645383778302406553/100000000000000000000)
  directionLo := (50711310208250177687/10000000000000000000)
  directionHi := (507113102082501776871/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree104.table
  base := (9300954146571249725264121325301771635589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137998839460580951660206847090000000000000)
      linear := (-122539084249805368457700640841091000000000000)
      constant := (3372537742312053013974254625503443557928398715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree104.table
  base := (9300954142462076501653093339264143486587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-1104088713508531556284153818490569000000000000)
      constant := (30419474356594633438856871526839889807094610605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50711310208250177687/10000000000000000000)
  centralHi := (507113102082501776871/100000000000000000000)
  directionLo := (509568869966293775241/100000000000000000000)
  directionHi := (254784434983146887621/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree105.table
  base := (48222817833772851562807802821501938275759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-6969384672369928601537271747631089250000000000)
      constant := (193729299229798840327554595787860832244728630359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree105.table
  base := (12055704454064367186133454659525494755257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3488600771208775927678398812488747750000000000)
      constant := (97077220387143561402104134868738153372604462114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509568869966293775241/100000000000000000000)
  centralHi := (254784434983146887621/50000000000000000000)
  directionLo := (512012859383153931121/100000000000000000000)
  directionHi := (256006429691576965561/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree106.table
  base := (624598816678120066121817776491480515039/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3517867132667077389978703697273692750000000000)
      constant := (98754529128061057159034661288248218215375065560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree106.table
  base := (12491976329829690549271913537914323589093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-95088945353802983588622538211939298000000000000)
      constant := (2672221518817576877592963872484321139869679177822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512012859383153931121/100000000000000000000)
  centralHi := (256006429691576965561/50000000000000000000)
  directionLo := (64305654775248613393/12500000000000000000)
  directionHi := (102889047640397781429/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree107.table
  base := (25870016615445658849699355497962578402271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-10653125787447571437566314562195522625000000000)
      constant := (301988354843367912283705394354198059950380539013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree107.table
  base := (51740033218164531567858721397271398056407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-191971339769938034259856616973364813500000000000)
      constant := (5447710576444659974273702480072782990362552739589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64305654775248613393/12500000000000000000)
  centralHi := (102889047640397781429/20000000000000000000)
  directionLo := (516866170341693820891/100000000000000000000)
  directionHi := (129216542585423455223/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree108.table
  base := (26769600760430336452685114293080293164271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3584216725631303568398839344189989000000000000)
      constant := (102589417073957331531598799577990669851678991671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree108.table
  base := (53539201510013337022343917674259990383493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-7176473660454448197869191019364853000000000000)
      constant := (205628611752872483644649939531170286400274657693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516866170341693820891/100000000000000000000)
  centralHi := (129216542585423455223/25000000000000000000)
  directionLo := (519275815900063460139/100000000000000000000)
  directionHi := (25963790795003173007/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree109.table
  base := (3460338137611895970703308484870428284969/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3617391522113416657608907167648137125000000000)
      constant := (104534425506459318395132582815297826659554858552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree109.table
  base := (55365410192545534273087373795716577297817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-195558237894602168425079698072337248500000000000)
      constant := (5657228860278245787570008668423263565285307715659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519275815900063460139/100000000000000000000)
  centralHi := (25963790795003173007/5000000000000000000)
  directionLo := (260837165638672140577/50000000000000000000)
  directionHi := (104334866255468856231/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree110.table
  base := (28609329635854406040645037946892397329927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-10951698955786589240456924973318855750000000000)
      constant := (319493430735621413820488218792428953594203411181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree110.table
  base := (57218659263830331830463232474944619484183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-197351686956934235507691238621823466000000000000)
      constant := (5763479605292065565138054269101005640390646998341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260837165638672140577/50000000000000000000)
  centralHi := (104334866255468856231/20000000000000000000)
  directionLo := (524061869294697009273/100000000000000000000)
  directionHi := (262030934647348504637/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree111.table
  base := (59098948728977916522551145098354086109037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-7367482230155285672058085629128866750000000000)
      constant := (216959142580255124863848519870301390363171516837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree111.table
  base := (59098948722264278184948307246733458283781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-22127237335474033621144753241256631500000000000)
      constant := (652302750262793992951423038306562656618334915543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524061869294697009273/100000000000000000000)
  centralHi := (262030934647348504637/50000000000000000000)
  directionLo := (263219289653911876023/50000000000000000000)
  directionHi := (526438579307823752047/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree112.table
  base := (3050313928612001235191379360439121319837/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3716915911559755925239110638022581500000000000)
      constant := (110479708641159905392046045763563379351147476370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree112.table
  base := (12201255713303877776569319810052557048651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-200938585081598369672914319720795901000000000000)
      constant := (5978964301494281377114356243072455670115370486885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263219289653911876023/50000000000000000000)
  centralHi := (526438579307823752047/100000000000000000000)
  directionLo := (13220115182899967471/2500000000000000000)
  directionHi := (528804607315998698841/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree113.table
  base := (62940648800373586675091438700961912755943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-22500544248251214086695070768884377750000000000)
      constant := (674989333789524197861921232595229910394694680429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree113.table
  base := (31470324397749702110270044297619564651531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-101366017071965218377762930135141059250000000000)
      constant := (3044099126338412852760547895695874851837236119137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13220115182899967471/2500000000000000000)
  centralHi := (528804607315998698841/100000000000000000000)
  directionLo := (66395012008340954477/12500000000000000000)
  directionHi := (531160096066727635817/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree114.table
  base := (1622551485311390143149849693516712310691/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3783265504523982103659246284938877750000000000)
      constant := (114535112261368686772295796348729780055136721820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree114.table
  base := (12980411881660580978753154789498468413507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-7575017896528240882893977808139568000000000000)
      constant := (229571355774466779686224990390636810498179696535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66395012008340954477/12500000000000000000)
  centralHi := (531160096066727635817/100000000000000000000)
  directionLo := (266752592578124288597/50000000000000000000)
  directionHi := (106701037031249715439/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree115.table
  base := (66890510407729995077556800797569422426727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (25012)
      previous := (12506)
      next := (12506)
      square := (121185761732097152382214843830000000000000)
      linear := (-14428885826110000729184552394695750000000000)
      constant := (440795381967750734672624170299112005827616863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree115.table
  base := (4180656900262013272885912362467143140273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1636007783383311557159900391705000000000000)
      linear := (-195008442597915473460065161974720750000000000)
      constant := (5963751759162412841934719522292326296317525592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266752592578124288597/50000000000000000000)
  centralHi := (106701037031249715439/20000000000000000000)
  directionLo := (535840011126073734407/100000000000000000000)
  directionHi := (66980001390759216801/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree116.table
  base := (4306625111598805847934514893283091804259/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-11548845292464624846238145795565522000000000000)
      constant := (355992063316591953962753355847061661006921412616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree116.table
  base := (13781200356513433765732543964957219996741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-208112381330926638003360481918740771000000000000)
      constant := (6421866518525066234113795637922461303365366689035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535840011126073734407/100000000000000000000)
  centralHi := (66980001390759216801/12500000000000000000)
  directionLo := (107632941511152350327/20000000000000000000)
  directionHi := (134541176888940437909/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree117.table
  base := (3547426677275508267598171542814240142687/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-22975088130001901605263016303629125000000000)
      constant := (714532780985373762432584957953877435823564230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree117.table
  base := (70948533542943033342212540178995739411047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379332946486860317220068949030000000000000)
      linear := (-46001716062515604884061368062289500000000000)
      constant := (1432188927877083785404789799381776964898443863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107632941511152350327/20000000000000000000)
  centralHi := (134541176888940437909/25000000000000000000)
  directionLo := (540479405152098571673/100000000000000000000)
  directionHi := (270239702576049285837/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree118.table
  base := (912726321088980372892321809215844907947/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-3915964690452434460499517578771470250000000000)
      constant := (122866435173444760398912163148657366633989789880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree118.table
  base := (73018105684931850246076917365994909009473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-211699279455590772168583563017713206000000000000)
      constant := (6649284039327097564982999614238915575604609183171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540479405152098571673/100000000000000000000)
  centralHi := (270239702576049285837/50000000000000000000)
  directionLo := (67848028979356925931/12500000000000000000)
  directionHi := (542784231834855407449/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree119.table
  base := (18778679552522267542208274682893516738011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-11847418460803642649128756206688855125000000000)
      constant := (374985619998798846100316475068565079243275778466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree119.table
  base := (37557359104113373333705802838520793112369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-106746364258961419625597551783599711750000000000)
      constant := (3382242201398109126315293954907833763804175326163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67848028979356925931/12500000000000000000)
  centralHi := (542784231834855407449/100000000000000000000)
  directionLo := (272539656409641516523/50000000000000000000)
  directionHi := (545079312819283033047/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree120.table
  base := (77238371114174755000515923916506735273677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-7964628566833321277839306451375533000000000000)
      constant := (254284708929963349838119535782338453640201997477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree120.table
  base := (772383711125887009330186458338315787199/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-11960343198903050351878146895371424500000000000)
      constant := (382259953794995467709803907269912942953706669850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272539656409641516523/50000000000000000000)
  centralHi := (545079312819283033047/100000000000000000000)
  directionLo := (109472954139098585839/20000000000000000000)
  directionHi := (136841192673873232299/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree121.table
  base := (19847266099796520153309558555479867777953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4015489079898773728129721049145914625000000000)
      constant := (129307878569582472615093274578271400923902302306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree121.table
  base := (79389064397835395339218928477378475627219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-217079626642586973416418184666171858500000000000)
      constant := (6997868335867757980024928243860537821094073157113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109472954139098585839/20000000000000000000)
  centralHi := (136841192673873232299/25000000000000000000)
  directionLo := (68705090688108460073/12500000000000000000)
  directionHi := (109928145100973536117/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree122.table
  base := (40783399032491001106231447848843432776091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-12145991629142660452019366617812188250000000000)
      constant := (394475336940187111046103413784071903653970934473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree122.table
  base := (4078339903191591358578342505967898484653/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-109436537852459520249514862607829038000000000000)
      constant := (3558025952734705531589379780545285336892644970310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68705090688108460073/12500000000000000000)
  centralHi := (109928145100973536117/20000000000000000000)
  directionLo := (275953647406817694121/50000000000000000000)
  directionHi := (551907294813635388243/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree123.table
  base := (41885786055730887322175306127194041054527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4081838672862999906549856696062210875000000000)
      constant := (133694055696416864761134164485581771601034518327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree123.table
  base := (83771572110482402842616152691988629825829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8172834250638929910431157991301640500000000000)
      constant := (267971476930172108216872579399094551213808938429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275953647406817694121/50000000000000000000)
  centralHi := (551907294813635388243/100000000000000000000)
  directionLo := (277082296891867847191/50000000000000000000)
  directionHi := (554164593783735694383/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree124.table
  base := (21500846634639541648122866887880332010863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4115013469345112995759924519520359000000000000)
      constant := (135914708718642950578933172785566211686706326126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree124.table
  base := (43001693268862141508332771239641328747089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-111229986914791587332126403157315255500000000000)
      constant := (3677701125401656936385075322604451384145599599603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277082296891867847191/50000000000000000000)
  centralHi := (554164593783735694383/100000000000000000000)
  directionLo := (139103183810274571861/25000000000000000000)
  directionHi := (111282547048219657489/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree125.table
  base := (88262241346231749105915545481497861121303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-24889129594963356509819954057871042750000000000)
      constant := (828922428280433191849651992558060105416629328509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree125.table
  base := (17652448269104356573100590173111107101997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-224253422891915241746864346864116728500000000000)
      constant := (7476569026535325778920703912440228419269710562595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139103183810274571861/25000000000000000000)
  centralHi := (111282547048219657489/20000000000000000000)
  directionLo := (139662957435362107899/25000000000000000000)
  directionHi := (558651829741448431597/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree126.table
  base := (90548136534466090397395866172172403320979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8362726124618678348360120332873310500000000000)
      constant := (280822287361407748880111405588276718498048843579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree126.table
  base := (45274068266930831101159322491372635115617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4186053184337913126471775692844499000000000000)
      constant := (140717226005752790384940982748329895514471275417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139662957435362107899/25000000000000000000)
  centralHi := (558651829741448431597/100000000000000000000)
  directionLo := (280440992816874060093/50000000000000000000)
  directionHi := (560881985633748120187/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree127.table
  base := (9286107210326371508007074735709579364497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4214537858791452263390127989894803375000000000)
      constant := (142686925620538090825743874260799826004295731485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree127.table
  base := (92861072102749166060381821256195019579191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-227840321016579375912087427963089163500000000000)
      constant := (7721885784129301238971399197717457382682029873957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280440992816874060093/50000000000000000000)
  centralHi := (560881985633748120187/100000000000000000000)
  directionLo := (56310330912137586103/10000000000000000000)
  directionHi := (563103309121375861031/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree128.table
  base := (47600524026321354072463034380220210173453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-12743137965820696057800587440058854500000000000)
      constant := (434943251598726968620438232428814357029150614959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree128.table
  base := (19040209610440939613515713170218628097261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-229633770078911442994698968512575381000000000000)
      constant := (7846035765991326704302351688073015610020636139235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56310330912137586103/10000000000000000000)
  centralHi := (563103309121375861031/100000000000000000000)
  directionLo := (565315904321142839421/100000000000000000000)
  directionHi := (282657952160571419711/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree129.table
  base := (48784032191316931330840512393304566080541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4280887451755678441810263636811099625000000000)
      constant := (147293618417817947048875295290027247805135195941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree129.table
  base := (48784032191130513674418675325800514640779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-12857067730069083893183917170114533250000000000)
      constant := (442843341660933676432121625443289927256325850137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565315904321142839421/100000000000000000000)
  centralHi := (282657952160571419711/50000000000000000000)
  directionLo := (141879968330059562613/25000000000000000000)
  directionHi := (567519873320238250453/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree130.table
  base := (3998484843731131438034847148985482825953/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (78292)
      previous := (39146)
      next := (39146)
      square := (379332946486860317220068949030000000000000)
      linear := (-51053991103405816935151851600819500000000000)
      constant := (1770704488464695868280628729572410979123228425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree130.table
  base := (99962121092960945198186132946332462089313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-1380003953867311107455160056873064000000000000)
      constant := (47913129797904396119407109641977333431021657579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141879968330059562613/25000000000000000000)
  centralHi := (567519873320238250453/100000000000000000000)
  directionLo := (284857658115595962753/50000000000000000000)
  directionHi := (569715316231191925507/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree131.table
  base := (102383218184625392280685340968779952575037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-26083422268319427721382395702364375250000000000)
      constant := (911842898631546559070928490830945918815795148511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree131.table
  base := (51191609092177650424817820192624057046797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-117507058632953822121266795080517016750000000000)
      constant := (4112226061919279875380586457654494607202223862119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284857658115595962753/50000000000000000000)
  centralHi := (569715316231191925507/100000000000000000000)
  directionLo := (35743895702808623731/6250000000000000000)
  directionHi := (571902331244937979697/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree132.table
  base := (52415677828365610686210683310591618036599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4380411841202017709440467107185544000000000000)
      constant := (154341479907793328978762032530887477056589987199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree132.table
  base := (104831355656501356719893308678237300593847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8770650604749618937968338174463713000000000000)
      constant := (309354804217596104336660632401517528910390515647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35743895702808623731/6250000000000000000)
  centralHi := (571902331244937979697/100000000000000000000)
  directionLo := (574081014682059060363/100000000000000000000)
  directionHi := (143520253670514765091/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree133.table
  base := (107306533509657031477253680629034811739583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8827173275368261597301069861287384250000000000)
      constant := (313455039365752493089983204416819943602767959783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree133.table
  base := (26826633377365353203857905852855487304849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-119300507695285889203878335630003234250000000000)
      constant := (4240850852977799262301758734277506741287328494246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574081014682059060363/100000000000000000000)
  centralHi := (143520253670514765091/25000000000000000000)
  directionLo := (57625146104228686521/10000000000000000000)
  directionHi := (576251461042286865211/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree134.table
  base := (109808751743468123787679593813326423277327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-26680568604997463327163616524611041500000000000)
      constant := (954791614583056589238792101280473272858498933381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree134.table
  base := (21961750348660331572207513113782624779799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-240394464452903845490368211809492686000000000000)
      constant := (8611818100080230641433200480399043677496739403865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57625146104228686521/10000000000000000000)
  centralHi := (576251461042286865211/100000000000000000000)
  directionLo := (115682752610466181457/20000000000000000000)
  directionHi := (289206881526165453643/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree135.table
  base := (112338010358232861700147782766032652161853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8959872461296713954141341155119976750000000000)
      constant := (323109456301391879682372461227787515721859320053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree135.table
  base := (112338010358091211343892055300619861487547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-8969922722786515280480731568851070500000000000)
      constant := (323812181342561407780121095159842901705598189347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115682752610466181457/20000000000000000000)
  centralHi := (289206881526165453643/50000000000000000000)
  directionLo := (580568011712104018933/100000000000000000000)
  directionHi := (290284005856052009467/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree136.table
  base := (114894309354021854145561975989785285739777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9026222054260940132561476802036273000000000000)
      constant := (327991793686877855407340211051573002330421803577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree136.table
  base := (114894309353901326268171395258412771997067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-243981362577567979655591292908465121000000000000)
      constant := (8875034094462552622919036607406414367191364245409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580568011712104018933/100000000000000000000)
  centralHi := (290284005856052009467/50000000000000000000)
  directionLo := (291357148169704897491/50000000000000000000)
  directionHi := (582714296339409794983/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree137.table
  base := (117477648730907277015800705496791984541569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-27277714941675498932944837346857707750000000000)
      constant := (998732651052449728554231347615812783512814930507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree137.table
  base := (117477648730804727141861225043408676297527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-245774811639900046738202833457951338500000000000)
      constant := (9008133694720590024381439047152456753287480705829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291357148169704897491/50000000000000000000)
  centralHi := (582714296339409794983/100000000000000000000)
  directionLo := (292426352306577032389/50000000000000000000)
  directionHi := (584852704613154064779/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree138.table
  base := (60044014244481155387835698407543191221561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 845000000000000000000000000000000000000000
      center := (12506)
      previous := (6253)
      next := (6253)
      square := (60592880866048576191107421915000000000000)
      linear := (-8656825368799047721551746782484750000000000)
      constant := (319344731846138548602379418089331783691443809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree138.table
  base := (120088028488875061706387209773292014034491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (75036)
      previous := (37518)
      next := (37518)
      square := (363557285196291457146644531490000000000000)
      linear := (-51999214598242409960263468600596000000000000)
      constant := (1920232660580434359873391971751293926115486937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292426352306577032389/50000000000000000000)
  centralHi := (584852704613154064779/100000000000000000000)
  directionLo := (586983322615139542071/100000000000000000000)
  directionHi := (73372915326892442759/12500000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree139.table
  base := (122725448628260675777770166833866546713281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9225270833153618667821883742785161750000000000)
      constant := (342859321514078470790303581897310496666151534681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree139.table
  base := (15340681078523306035742093105442596843621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-124680854882282090451712957278461886750000000000)
      constant := (4638658050685652710329247643269027851548113590268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586983322615139542071/100000000000000000000)
  centralHi := (73372915326892442759/12500000000000000000)
  directionLo := (147276558717625005159/25000000000000000000)
  directionHi := (589106234870500020637/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree140.table
  base := (6269495457443812484562403336601507738053/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1341015000000000000000000000000000000000000000
      center := (19847022)
      previous := (9923511)
      next := (9923511)
      square := (96160901934419090415287478579105000000000000)
      linear := (-13937430639176767269363029084552187000000000000)
      constant := (521833004020122260043803042512161951486190287590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree140.table
  base := (125389909148813103474130297412861652960919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-251155158826896247986037455106409991000000000000)
      constant := (9413398907764341470302796485623192220181696227013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147276558717625005159/25000000000000000000)
  centralHi := (589106234870500020637/100000000000000000000)
  directionLo := (2956107621934139261/500000000000000000)
  directionHi := (591221524386827852201/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree141.table
  base := (1601017625636034423722446742327083823193/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4678985009541035512331077518308877125000000000)
      constant := (176477384895615141451628644417357708971809845720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree141.table
  base := (128081410050829037272986833200736885957057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9368466958860307965505518357625785500000000000)
      constant := (353721337637138325319676526249225206810196852857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2956107621934139261/500000000000000000)
  centralHi := (591221524386827852201/100000000000000000000)
  directionLo := (74166159086505744083/12500000000000000000)
  directionHi := (118665854538409190533/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree142.table
  base := (65399975667176748884783263817922627605011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4712159806023148601541145341767025250000000000)
      constant := (179028811423765676671824622190166580314890588411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree142.table
  base := (65399975667153902411051721102242654469547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-127371028475780191075630268102691213000000000000)
      constant := (4844273863343331455012926340406339463097763226369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74166159086505744083/12500000000000000000)
  centralHi := (118665854538409190533/20000000000000000000)
  directionLo := (595429559871073224281/100000000000000000000)
  directionHi := (297714779935536612141/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree143.table
  base := (5341821319974446859344616987182661741643/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15870000000000000000000000000000000000000000
      center := (234876)
      previous := (117438)
      next := (117438)
      square := (1137998839460580951660206847090000000000000)
      linear := (-168473417840423491979333011783142250000000000)
      constant := (6447288080159607395116511037134325924912186025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree143.table
  base := (133545532999322305563024555964145708299311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 142830000000000000000000000000000000000000000
      center := (2113884)
      previous := (1056942)
      next := (1056942)
      square := (10241989555145228564941861623810000000000000)
      linear := (-1517961574046700883040663176064311500000000000)
      constant := (58151560587078708971164738298372689057889059013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595429559871073224281/100000000000000000000)
  centralHi := (297714779935536612141/50000000000000000000)
  directionLo := (298761232300665023729/50000000000000000000)
  directionHi := (597522464601330047459/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree144.table
  base := (17039769380747209936979850219591065869023/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4778509398987374779961280988683321500000000000)
      constant := (184186793397808150488630756227295217019026100892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree144.table
  base := (136318155045944622124189424803687408712017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9567739076897204308017911752013143000000000000)
      constant := (369173116807104648034406967179916780026263031817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298761232300665023729/50000000000000000000)
  centralHi := (597522464601330047459/100000000000000000000)
  directionLo := (599608064187128378819/100000000000000000000)
  directionHi := (29980403209356418941/5000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree145.table
  base := (13911781747427400803665042925223225274863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4811684195469487869171348812141469625000000000)
      constant := (186793348843706476370364318977291959981958885315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree145.table
  base := (139117817474245892427207936858319814933681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-260122404138556583399095157853841078500000000000)
      constant := (10108728970413405667068200536558732867828172407187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599608064187128378819/100000000000000000000)
  centralHi := (29980403209356418941/5000000000000000000)
  directionLo := (15042160864824724631/2500000000000000000)
  directionHi := (601686434592988985241/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree146.table
  base := (141944520284320121036425662796604192049341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-29069153951709605750288499813597706500000000000)
      constant := (1136509683573162280181912956281816545776459404223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree146.table
  base := (14194452028429620954062685148534368086169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-130957926600444325240853349201663648000000000000)
      constant := (5125389094540605759542924529513539539509165293815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15042160864824724631/2500000000000000000)
  centralHi := (601686434592988985241/100000000000000000000)
  directionLo := (603757650475926440251/100000000000000000000)
  directionHi := (150939412618981610063/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree147.table
  base := (28959652695236975954245623536475757357697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9756067576867428095182968918115531750000000000)
      constant := (384123177306545879203929918143423091566114847485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree147.table
  base := (28959652695232908934487728189116564957731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-29301033584802301951590915439201501500000000000)
      constant := (1154869089977267726394000947400302141013041636965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603757650475926440251/100000000000000000000)
  centralHi := (150939412618981610063/25000000000000000000)
  directionLo := (75727723152092587937/12500000000000000000)
  directionHi := (605821785216740703497/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree148.table
  base := (4614970220310499445748337911903507343647/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4911208584915827136801552282515914000000000000)
      constant := (194723273016947181220774868657457582172970167152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree148.table
  base := (147679047049918689422360531365796571281779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-265502751325552784646929779502299731000000000000)
      constant := (10537859832556163359642449572075530518267382758233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75727723152092587937/12500000000000000000)
  centralHi := (605821785216740703497/100000000000000000000)
  directionLo := (303939455475176195117/50000000000000000000)
  directionHi := (121575782190070478047/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree149.table
  base := (150586871005639919104198416775620524641291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-29666300288387641356069720635844372750000000000)
      constant := (1184420002119316462296098287894299819015680670073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree149.table
  base := (150586871005625214030479749293851614760321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-267296200387884851729541320051785948500000000000)
      constant := (10682892257363633674418091225241870245858311358467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303939455475176195117/50000000000000000000)
  centralHi := (121575782190070478047/20000000000000000000)
  directionLo := (609929098595217210823/100000000000000000000)
  directionHi := (76241137324402151353/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree150.table
  base := (76760867671680971440162475975361112969911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-4977558177880053315221687929432210250000000000)
      constant := (200101770662092543911014679667245020969998013311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree150.table
  base := (6140869413733977555121563539769445913743/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-9966283312970996993042698540787858000000000000)
      constant := (401071077193258450147141764268366358978363448575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609929098595217210823/100000000000000000000)
  centralHi := (76241137324402151353/12500000000000000000)
  directionLo := (611972417881853514887/100000000000000000000)
  directionHi := (76496552235231689361/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree151.table
  base := (156483640063166048863853846698948602607373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-10021465948724332808863511505780716750000000000)
      constant := (405637167887138884852809351014063638857639253573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree151.table
  base := (39120910015788854233490913994221999672371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-135441549256274492947382200575379191750000000000)
      constant := (5487970156559675705546240193183036027934445547634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611972417881853514887/100000000000000000000)
  centralHi := (76496552235231689361/12500000000000000000)
  directionLo := (76751117172564425843/12500000000000000000)
  directionHi := (122801787476103081349/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree152.table
  base := (159472585165114964963811820098300572491551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-30263446625065676961850941458091039000000000000)
      constant := (1233322641185917459386502906147339271443951452853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree152.table
  base := (79736292582552962604949740895932065343037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-136338273787440526488687970850122300500000000000)
      constant := (5561977972033952489311369990190025092990786972599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76751117172564425843/12500000000000000000)
  centralHi := (122801787476103081349/20000000000000000000)
  directionLo := (616038724528042503357/100000000000000000000)
  directionHi := (308019362264021251679/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree153.table
  base := (8124428532463507464310557146052100866463/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5077082567326392582851891399806654625000000000)
      constant := (208307339424345693533119907729474780051095336630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree153.table
  base := (81244285324631231798881536636405959871061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5082777715503946667777545967587607750000000000)
      constant := (208758629204884950123392806748805224577807724461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616038724528042503357/100000000000000000000)
  centralHi := (308019362264021251679/50000000000000000000)
  directionLo := (618061845653916079477/100000000000000000000)
  directionHi := (309030922826958039739/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree154.table
  base := (41382899128922948475517774300342257672281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5110257363808505672061959223264802750000000000)
      constant := (211079281623650483948183543038356106340694187362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree154.table
  base := (82765798257842629863066531709505428228689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-138131722849772593571299511399608518000000000000)
      constant := (5711485206053571887144952107244559847242471682803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618061845653916079477/100000000000000000000)
  centralHi := (309030922826958039739/50000000000000000000)
  directionLo := (62007836600555008303/10000000000000000000)
  directionHi := (620078366005550083031/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree155.table
  base := (168601662764438833653278975201308908392497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-30860592961743712567632162280337705250000000000)
      constant := (1283217600773419493359047039153755651477905372891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree155.table
  base := (168601662764433278692885939644183471518247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-278056894761877254225210563348703253500000000000)
      constant := (11573969249198116713048129838525366502910725601269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62007836600555008303/10000000000000000000)
  centralHi := (620078366005550083031/100000000000000000000)
  directionLo := (622088349772844303443/100000000000000000000)
  directionHi := (155522087443211075861/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree156.table
  base := (85849384697784479508001124486811902824029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-30630810395104922192201744793971000000000000)
      constant := (1282120088402997438823803090389223559093911341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree156.table
  base := (42924692348891059179433082847242289723143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7935000000000000000000000000000000000000000
      center := (117438)
      previous := (58719)
      next := (58719)
      square := (568999419730290475830103423545000000000000)
      linear := (-91995510790338369923675905291975500000000000)
      constant := (3854688523450639526596766563469767527581255882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622088349772844303443/100000000000000000000)
  centralHi := (155522087443211075861/25000000000000000000)
  directionLo := (312045930056012916673/50000000000000000000)
  directionHi := (624091860112025833347/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree157.table
  base := (21852864551142329025222785834842831355147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5209781753254844939692162693639247125000000000)
      constant := (219505366057262962641415195216269878375644737788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree157.table
  base := (174822916409134617915188623307608660029721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-281643792886541388390433644447675688500000000000)
      constant := (11878950129523466297748297098358910608669811352267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312045930056012916673/50000000000000000000)
  centralHi := (624091860112025833347/100000000000000000000)
  directionLo := (626088959168803876541/100000000000000000000)
  directionHi := (313044479584401938271/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree158.table
  base := (177974103805203105811552315313493364698961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-31457739298421748173413383102584371500000000000)
      constant := (1334104880882249430915839646362825634298605437083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree158.table
  base := (44493525951299923380153201067384090006857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-141718620974436727736522592498580953000000000000)
      constant := (6016466086379056350885579971787870032845463223478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626088959168803876541/100000000000000000000)
  centralHi := (313044479584401938271/50000000000000000000)
  directionLo := (628079708100861919573/100000000000000000000)
  directionHi := (314039854050430959787/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree159.table
  base := (181152331583816443471581108188148983028087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-10552262692438142236224596681111086750000000000)
      constant := (450429274418889622732045974219475646692631505887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree159.table
  base := (7246093263352541720524779378706064988773/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-10564099667081686020579878723949930500000000000)
      constant := (451404022890404266314177229774208032870282374325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628079708100861919573/100000000000000000000)
  centralHi := (314039854050430959787/50000000000000000000)
  directionLo := (9844752610932973401/1562500000000000000)
  directionHi := (126012833419942059533/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree160.table
  base := (46089399936257885494021595627952573720549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5309306142701184207322366164013691500000000000)
      constant := (228096837244475045794714262432175941086381602298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree160.table
  base := (184357599745029076672738612289190406965603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-287024140073537589638268266096134341000000000000)
      constant := (12343879465372001480145686729568257672474560592681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9844752610932973401/1562500000000000000)
  centralHi := (126012833419942059533/20000000000000000000)
  directionLo := (316021197705960622867/50000000000000000000)
  directionHi := (126408479082384249147/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree161.table
  base := (187589908288900154541805475190878271222821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5070000000000000000000000000000000000000000
      center := (75036)
      previous := (37518)
      next := (37518)
      square := (363557285196291457146644531490000000000000)
      linear := (-60595246947258570471067304205729750000000000)
      constant := (2620008471668823310019416268690017416322470247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree161.table
  base := (23448738536112257398482125085314789785159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22815000000000000000000000000000000000000000
      center := (337662)
      previous := (168831)
      next := (168831)
      square := (1636007783383311557159900391705000000000000)
      linear := (-272984488786266216182306055430643250000000000)
      constant := (11815543208649807676523950090839675746283722068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316021197705960622867/50000000000000000000)
  centralHi := (126408479082384249147/20000000000000000000)
  directionLo := (63401445135976762913/10000000000000000000)
  directionHi := (634014451359767629131/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree162.table
  base := (19084925721547291484753399305531114660609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5375655735665410385742501810929987750000000000)
      constant := (233916366232425702832774805904822154768240526045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree162.table
  base := (190849257215471133995112071804375056268923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-10763371785118582363092272118337288000000000000)
      constant := (468844606154797131845461881568011526030497985123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63401445135976762913/10000000000000000000)
  centralHi := (634014451359767629131/100000000000000000000)
  directionLo := (158995098090321423587/25000000000000000000)
  directionHi := (635980392361285694349/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree163.table
  base := (194135646524799361588553602947815114219393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-10817661064295046949905139268776271750000000000)
      constant := (473707390370701206394703030453670373924765453593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree163.table
  base := (194135646524797848089460331723676078070939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-292404487260533790886102887744592993500000000000)
      constant := (12817758419656199192215276426426872453407990473553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158995098090321423587/25000000000000000000)
  centralHi := (635980392361285694349/100000000000000000000)
  directionLo := (318970137474890682537/50000000000000000000)
  directionHi := (25517610997991254603/4000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree164.table
  base := (197449076216927963323662838419376639706681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-32652031971777819384975824747077704000000000000)
      constant := (1438856402665468736975527417027229015774250964243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree164.table
  base := (49362269054231669272194792141860460072247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12069135000000000000000000000000000000000000000
      center := (178623198)
      previous := (89311599)
      next := (89311599)
      square := (865448117409771813737587307211945000000000000)
      linear := (-147098968161432928984357214147039605500000000000)
      constant := (6488853437590821715340515095265271049509623518538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318970137474890682537/50000000000000000000)
  centralHi := (25517610997991254603/4000000000000000000)
  directionLo := (639894154792798831473/100000000000000000000)
  directionHi := (319947077396399415737/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree165.table
  base := (100394773145953071716315182711741464749101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5475180125111749653372705281304432125000000000)
      constant := (242783482009110381577271317990384956639253128501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree165.table
  base := (200789546291905050376480622281660011885729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-32887931709466436116813996538173936500000000000)
      constant := (1459849970306218862394556158754891524074038174987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639894154792798831473/100000000000000000000)
  centralHi := (319947077396399415737/50000000000000000000)
  directionLo := (40115130419410589917/6250000000000000000)
  directionHi := (641842086710569438673/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree166.table
  base := (102078528374890152517758072572776546767289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5508354921593862742582773104762580250000000000)
      constant := (245775939879949453684070000979344375916917403889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree166.table
  base := (204157056749779376178402119303044733788479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-297784834447529992133937509393051646000000000000)
      constant := (13300586992379290206253750618760771691001442899133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40115130419410589917/6250000000000000000)
  centralHi := (641842086710569438673/100000000000000000000)
  directionLo := (643784124693958172107/100000000000000000000)
  directionHi := (160946031173489543027/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree167.table
  base := (41510321518119171150694297327200037198357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2682030000000000000000000000000000000000000000
      center := (39694044)
      previous := (19847022)
      next := (19847022)
      square := (192321803868838180830574957158210000000000000)
      linear := (-33249178308455854990757045569324370250000000000)
      constant := (1492720644340584213358119355369746495141367212355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree167.table
  base := (207551607590595066457689390229174610966507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24138270000000000000000000000000000000000000000
      center := (357246396)
      previous := (178623198)
      next := (178623198)
      square := (1730896234819543627475174614423890000000000000)
      linear := (-299578283509862059216549049942537863500000000000)
      constant := (13463518654051714381412029929881947393321700692289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643784124693958172107/100000000000000000000)
  centralHi := (160946031173489543027/25000000000000000000)
  directionLo := (322860160960962180547/50000000000000000000)
  directionHi := (129144064384384872219/20000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree168.table
  base := (210973198814397232214194221823352567075733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (13231348)
      previous := (6615674)
      next := (6615674)
      square := (64107267956279393610191652386070000000000000)
      linear := (-11149409029116177842005817503357753000000000000)
      constant := (503631969079112227087194799346692516849137605933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree168.table
  base := (2109731988143965615343426532959205468101/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 447005000000000000000000000000000000000000000
      center := (6615674)
      previous := (3307837)
      next := (3307837)
      square := (32053633978139696805095826193035000000000000)
      linear := (-5580958010596187524058529453556001500000000000)
      constant := (252360087366173139967965713498910895902684875050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell099.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322860160960962180547/50000000000000000000)
  centralHi := (129144064384384872219/20000000000000000000)
  directionLo := (129530146155702515197/20000000000000000000)
  directionHi := (323825365389256287993/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree169.table
  base := (53605457605306981056226493738212269542947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (39146)
      previous := (19573)
      next := (19573)
      square := (189666473243430158610034474515000000000000)
      linear := (-33182717816805929054514654290751625000000000)
      constant := (1508068469398388352970001375911740842895187926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11153
  qDenominator := 21528
  table := BinomialMassData.Q11153_21528.Degree169.table
  base := (107210915210613677177634402900009860208587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71415000000000000000000000000000000000000000
      center := (1056942)
      previous := (528471)
      next := (528471)
      square := (5120994777572614282470930811905000000000000)
      linear := (-896938407202740217105834707223403250000000000)
      constant := (40805814152497931128040413760708833911484248121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11153_21528.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell099.Kernel169
