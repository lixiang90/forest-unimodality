import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell043.Parameters
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch000_049
import ForestUnimodality.BinomialMassData.Q2983_6208.Batch050_099
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch000_049
import ForestUnimodality.BinomialMassData.Q4487_9312.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree000.table
  base := (199412286663361841504382707/5000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30608239848411107619785555000000000000)
      linear := (1220073016492765607607373650000000000)
      constant := (9970614333168092075219135350000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree000.table
  base := (199412286663361841504382707/5000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (30608239848411107619785555000000000000)
      linear := (1220073016492765607607373650000000000)
      constant := (9970614333168092075219135350000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree001.table
  base := (114573160860202977318347829646695466380007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-5305734664992392868518300754546125000000000)
      constant := (1079238436381888024234067340040988704692923363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree001.table
  base := (57167842779652450571048231289466719444299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-23945391912746140035811709618152875000000000)
      constant := (4846550237227817203031530444285916907934558619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49961995729029094919/100000000000000000000)
  directionHi := (1249049893225727373/2500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree002.table
  base := (135878952318884913873857781117257397165711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-21682125340456788738152314165098500000000000)
      constant := (1288682875838537837581647251160374779619674799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree002.table
  base := (27071306000754067108789363986484745310883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-39139163085270815132641135453489800000000000)
      constant := (2310886255462310814973530815769867286420883323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49961995729029094919/100000000000000000000)
  centralHi := (1249049893225727373/2500000000000000000)
  directionLo := (35328465981609798181/50000000000000000000)
  directionHi := (70656931963219596363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree003.table
  base := (83774449303783558280648823371547931729153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-32752781350928791739268026821104750000000000)
      constant := (811509838820319284815787279615807909561475577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree003.table
  base := (83335798968125383241631972915193844496841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-32845562577969287909240501784698500000000000)
      constant := (807514662106427112844619479259532312558276969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35328465981609798181/50000000000000000000)
  centralHi := (70656931963219596363/100000000000000000000)
  directionLo := (86536715050217642091/100000000000000000000)
  directionHi := (21634178762554410523/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree004.table
  base := (53942232598469877868797893138566027545091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-43823437361400794740383739477111000000000000)
      constant := (549216293768089808190913933985670346921761219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree004.table
  base := (53605917328470099738998516921490548447503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-395524310977093106703123354857124000000000000)
      constant := (4916587875935669100835248477536577758083001543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86536715050217642091/100000000000000000000)
  centralHi := (21634178762554410523/25000000000000000000)
  directionLo := (99923991458058189839/100000000000000000000)
  directionHi := (1249049893225727373/1250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree005.table
  base := (36252751568695045739325638783734687026283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-54894093371872797741499452133117250000000000)
      constant := (406493298764202195414530494740227121402171747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree005.table
  base := (18000707828756300394783665863566362071239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-247719279376231311111541096825980750000000000)
      constant := (1820238455836262640346287595873908165148339759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/100000000000000000000)
  centralHi := (1249049893225727373/1250000000000000000)
  directionLo := (13964802342707902391/12500000000000000000)
  directionHi := (111718418741663219129/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree006.table
  base := (25251902551301861587635791435763783914037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-65964749382344800742615164789123500000000000)
      constant := (332023192442010348820690668069509435034674133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree006.table
  base := (25061926912124315197124288238477929572319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-66150311836425793082560114716311000000000000)
      constant := (330767747176582446411882976687863433095949471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13964802342707902391/12500000000000000000)
  centralHi := (111718418741663219129/100000000000000000000)
  directionLo := (61190698033616860211/50000000000000000000)
  directionHi := (122381396067233720423/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree007.table
  base := (18003764920903045553060520865658372506911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-77035405392816803743730877445129750000000000)
      constant := (298181897637245352200370839348903843714400599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree007.table
  base := (8927527570514375704633600888754839048507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-347633527151600826631499935620818250000000000)
      constant := (1338784046567887365364696936073163677810371267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61190698033616860211/50000000000000000000)
  centralHi := (122381396067233720423/100000000000000000000)
  directionLo := (132187015703482203447/100000000000000000000)
  directionHi := (16523376962935275431/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree008.table
  base := (6459690366427961322756747747779863273033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-44053030701644403372423295050568000000000000)
      constant := (145009454524382138285924357381168796035967497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree008.table
  base := (12797366357979259961116714381214476519929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-795181302078571168782958710036474000000000000)
      constant := (2608365243922770896424467525948540086184107649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132187015703482203447/100000000000000000000)
  centralHi := (16523376962935275431/12500000000000000000)
  directionLo := (5652554557057567709/4000000000000000000)
  directionHi := (70656931963219596363/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree009.table
  base := (1141589144428821361565086694878347519629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-12397089676720101218245287844642781250000000)
      constant := (37423210765852535762014527938670836411798636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree009.table
  base := (225692334137159560584405522573605671493/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2352250000000000000000000000000000000000000
      center := (18818)
      previous := (9409)
      next := (9409)
      square := (287992928733700111594562286995000000000000)
      linear := (-2486376527372057456396993191198087500000000)
      constant := (7489935215276738015391394253261393067765137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5652554557057567709/4000000000000000000)
  centralHi := (70656931963219596363/50000000000000000000)
  directionLo := (149885987187087284759/100000000000000000000)
  directionHi := (3747149679677182119/2500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree010.table
  base := (6166547244994486338541593107294285895089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-110247373424232812747078015413148500000000000)
      constant := (321792113466775151055492594574058928174392401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree010.table
  base := (6072423732057896167309832546413573437827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-995009797629310199822876387626149000000000000)
      constant := (2901496419555146193654713288664771406038628187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/100000000000000000000)
  centralHi := (3747149679677182119/2500000000000000000)
  directionLo := (7899685147566834391/5000000000000000000)
  directionHi := (157993702951336687821/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree011.table
  base := (1876671488736973202442457321653679946409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-60659014717352407874096864034577375000000000)
      constant := (177360453491059607853535789584312450201699781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree011.table
  base := (146658214079559902100591868005779273993/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-218984809080935943068567045284197300000000000)
      constant := (640255071735228788738591220905595671942506165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7899685147566834391/5000000000000000000)
  centralHi := (157993702951336687821/100000000000000000000)
  directionLo := (33141038722105700917/20000000000000000000)
  directionHi := (82852596805264252293/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree012.table
  base := (27173564321229729376485006941414744751/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-16548585680647102343663680090645125000000000)
      constant := (49590394215176169093433408767386744885647272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree012.table
  base := (1657353729165417613959853996312412883589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-132759810353338803429199340579536000000000000)
      constant := (398089465477462947269757589359663617821688901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/20000000000000000000)
  centralHi := (82852596805264252293/50000000000000000000)
  directionLo := (173073430100435284183/100000000000000000000)
  directionHi := (21634178762554410523/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree013.table
  base := (15880452334002737836470355561567488801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-71729670727824410875212576690583625000000000)
      constant := (223466228213784144178796148053334248463066109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree013.table
  base := (-9202157700303654492108644191739508073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-258950508191083749276550580802132300000000000)
      constant := (807673792269938576603083601348902605154370287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/100000000000000000000)
  centralHi := (21634178762554410523/12500000000000000000)
  directionLo := (9007026871276361939/5000000000000000000)
  directionHi := (180140537425527238781/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree014.table
  base := (-1426655384974905677975103960225734601307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-154529997466120824751540866037173500000000000)
      constant := (504803500258353483279039351197692992823802437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree014.table
  base := (-375259108674290625057863607145894644301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-348666697182697065475677935701374750000000000)
      constant := (1140776533751753422605761722621495894063447019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9007026871276361939/5000000000000000000)
  centralHi := (180140537425527238781/100000000000000000000)
  directionLo := (23367583797186227977/12500000000000000000)
  directionHi := (186940670377489823817/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree015.table
  base := (-2674963085697527866896430555063907270043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-165600653476592827752656578693179750000000000)
      constant := (569971005879486517429189041717782319543040413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree015.table
  base := (-1373116333037661099567202482518885487273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-83032279805897654301259476755574250000000000)
      constant := (286319760609457105894093089348552052543998343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/12500000000000000000)
  centralHi := (186940670377489823817/100000000000000000000)
  directionLo := (24187747175226971863/12500000000000000000)
  directionHi := (38700395480363154981/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree016.table
  base := (-748194374574006423754285308990284566619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-35334261897412966150754458269837200000000000)
      constant := (128434662411081890321719320389405612512681829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree016.table
  base := (-952311122065242916169716716865382586257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-398623821070381823235657355098793500000000000)
      constant := (1451994155629501770427316639632824787213170983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24187747175226971863/12500000000000000000)
  centralHi := (38700395480363154981/20000000000000000000)
  directionLo := (99923991458058189839/50000000000000000000)
  directionHi := (199847982916116379679/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree017.table
  base := (-4645908768764091227672786920856090928579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-187741965497536833754888004005192250000000000)
      constant := (721210693733568116497832044715414100999875189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree017.table
  base := (-4711220831325662390573303964467522177471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-1694409532056896808462588259190011500000000000)
      constant := (6523978017102962165231093315787321059177078249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99923991458058189839/50000000000000000000)
  centralHi := (199847982916116379679/100000000000000000000)
  directionLo := (51499646414361347701/25000000000000000000)
  directionHi := (41199717131489078161/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree018.table
  base := (-1351715163113020891055963601267326754991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-49703155377002209189000929165299625000000000)
      constant := (201730595117192626001925084587225173734164681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree018.table
  base := (-34182620094176498001728340102216204983/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2352250000000000000000000000000000000000000
      center := (18818)
      previous := (9409)
      next := (9409)
      square := (287992928733700111594562286995000000000000)
      linear := (-4984232721756295344395964161069025000000000)
      constant := (20278653963586130937547110276138155753009812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/25000000000000000000)
  centralHi := (41199717131489078161/20000000000000000000)
  directionLo := (6624087371551837159/3125000000000000000)
  directionHi := (211970795889658789089/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree019.table
  base := (-6038143964955884282763124411666456503011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-209883277518480839757119429317204750000000000)
      constant := (899173668867441790811030579496452543185044501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree019.table
  base := (-6097552797200288313120470195993220735941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-1894238027607635839502505936779686500000000000)
      constant := (8135776799373967287868260071623899192047280179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/3125000000000000000)
  centralHi := (211970795889658789089/100000000000000000000)
  directionLo := (217779290400448565969/100000000000000000000)
  directionHi := (21777929040044856597/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree020.table
  base := (-3276046462119690773217424407895118879257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-110476966764476421379117570986605500000000000)
      constant := (498924253136379876590399251132425998340070887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree020.table
  base := (-413035334613508277406358235685775266993/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-249269034422875669377808096946815500000000000)
      constant := (1128664606406049894123742401826738307356531534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/100000000000000000000)
  centralHi := (21777929040044856597/10000000000000000000)
  directionLo := (223436837483326438257/100000000000000000000)
  directionHi := (111718418741663219129/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree021.table
  base := (-3479765224247311743104328012451791873733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-116012294769712422879675427314608625000000000)
      constant := (551422529923727705126355436484140159595983703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree021.table
  base := (-70130946833988208498166965764526231683/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704500000000000000000000000000000000000000
      center := (37636)
      previous := (18818)
      next := (18818)
      square := (575985857467400223189124573990000000000000)
      linear := (-11633702906435415947457908968718675000000000)
      constant := (55444543482783109322268880504405184914848265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/100000000000000000000)
  centralHi := (111718418741663219129/50000000000000000000)
  directionLo := (57238656824834053731/25000000000000000000)
  directionHi := (9158185091973448597/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree022.table
  base := (-7270064094692068901725785728664410594809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-243095245549896848760466567285223500000000000)
      constant := (1214072932087993715180943267366746177900942119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree022.table
  base := (-7320764426066934760898912922904968894177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-2193980770933744386062382453164199000000000000)
      constant := (10987064786862767287154999195681977172822197463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57238656824834053731/25000000000000000000)
  centralHi := (9158185091973448597/4000000000000000000)
  directionLo := (234342532159668944469/100000000000000000000)
  directionHi := (23434253215966894447/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree023.table
  base := (-3746141931509522973746598349400661763303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-127082950780184425880791139970614875000000000)
      constant := (665725649841306048679869855188527563117519573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree023.table
  base := (-7540179733968160504416306244666359323561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-2293895018709113901582341291959036500000000000)
      constant := (12049729038244803754093088735575953580809030959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/100000000000000000000)
  centralHi := (23434253215966894447/10000000000000000000)
  directionLo := (239609314084893192001/100000000000000000000)
  directionHi := (119804657042446596001/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree024.table
  base := (-7633903540136652216624007742609841185681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-265236557570840854762697992597236000000000000)
      constant := (1454907583612616289535498867141363629283927471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree024.table
  base := (-7679067616297529314139463709696818751471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-265978807387164824122477792305986000000000000)
      constant := (1463039583353491626546193335389426632367409361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239609314084893192001/100000000000000000000)
  centralHi := (119804657042446596001/50000000000000000000)
  directionLo := (48952558426893488169/20000000000000000000)
  directionHi := (122381396067233720423/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree025.table
  base := (-1925467082015331125021113718170481479641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-69076803395328214440953426313310562500000000)
      constant := (396094109118058409485504855754298478332276581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree025.table
  base := (-7744384203353211859165064760547831901681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-2493723514259852932622258969548711500000000000)
      constant := (14339357370602850551193177132593933226421251239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/20000000000000000000)
  centralHi := (122381396067233720423/50000000000000000000)
  directionLo := (124904989322572737299/50000000000000000000)
  directionHi := (249809978645145474599/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree026.table
  base := (-1540488261228869957219494224412397490487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-57475573918356972152985883581849700000000000)
      constant := (343959785789569576661422360219326225449507817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree026.table
  base := (-774240118419143073955806448704764404191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10367745434413204017404242331820000000000000)
      linear := (-259363776203522244814221780834354900000000000)
      constant := (1556520130660811150492929961588148854863701929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124904989322572737299/50000000000000000000)
  centralHi := (249809978645145474599/100000000000000000000)
  directionLo := (127378595580179364343/50000000000000000000)
  directionHi := (254757191160358728687/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree027.table
  base := (-3820637881552760396886555391381595311489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-149224262801128431883022565282627375000000000)
      constant := (930560934622947247968334750273061701550137499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree027.table
  base := (-7678778286622178356214190416588089403541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-299283556645621329295797405237598500000000000)
      constant := (1871600976309614392624872929513381971489582731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127378595580179364343/50000000000000000000)
  centralHi := (254757191160358728687/100000000000000000000)
  directionLo := (10384405806026117051/4000000000000000000)
  directionHi := (64902536287663231569/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree028.table
  base := (-3761738723370123776680357929604222847291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-154759590806364433383580421610630500000000000)
      constant := (1004148608692683231428038231223027789104838981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree028.table
  base := (-1889656438073169522157528011794359252749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-698366564396490369795533871483306000000000000)
      constant := (4544136767691294028569422478012485645367961931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10384405806026117051/4000000000000000000)
  centralHi := (64902536287663231569/25000000000000000000)
  directionLo := (52874806281392881379/20000000000000000000)
  directionHi := (16523376962935275431/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree029.table
  base := (-7353659146695914012524719109650167533539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-320589837623200869768276555877267250000000000)
      constant := (2161281571628471548501758038974030681098806549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree029.table
  base := (-295462366801584552396907773106665245089/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-578676101072266198940418864945612300000000000)
      constant := (3912245061173154403966278202887271250340591955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52874806281392881379/20000000000000000000)
  centralHi := (16523376962935275431/6250000000000000000)
  directionLo := (10762143243766875203/4000000000000000000)
  directionHi := (67263395273542970019/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree030.table
  base := (-7135989125190692508259969156192393937697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-331660493633672872769392268533273500000000000)
      constant := (2320035712795998969354929699444671820127708927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree030.table
  base := (-7166748154697475166945966325806366790443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-332588305904077834469117018169211000000000000)
      constant := (2333121156103835314722190404143720238618721813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10762143243766875203/4000000000000000000)
  centralHi := (67263395273542970019/25000000000000000000)
  directionLo := (273653120787660021997/100000000000000000000)
  directionHi := (136826560393830010999/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree031.table
  base := (-6874234405524578710017693420793883622389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-342731149644144875770507981189279750000000000)
      constant := (2484524196965719066161724845044769034543816899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree031.table
  base := (-1380591973489778859125242966377059106269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-618641800182414005148402400463547300000000000)
      constant := (4497364672199061416076056777786577393759534811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273653120787660021997/100000000000000000000)
  centralHi := (136826560393830010999/50000000000000000000)
  directionLo := (139088309657976977641/50000000000000000000)
  directionHi := (278176619315953955283/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree032.table
  base := (-6571799637840813369218933181997460531383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-353801805654616878771623693845286000000000000)
      constant := (2654714989784434086692022898384512893860217353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree032.table
  base := (-412412380698897299914982581865531449731/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-399140406085929942657746355139071750000000000)
      constant := (3003391992288669989269108947338279612610658378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139088309657976977641/50000000000000000000)
  centralHi := (278176619315953955283/100000000000000000000)
  directionLo := (282627727852878385451/100000000000000000000)
  directionHi := (70656931963219596363/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree033.table
  base := (-1557940522107648516675995794191985285229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-91218115416272220443184851625323062500000000)
      constant := (707644784313402538226924381570950359962999089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree033.table
  base := (-6256738405393050298203062366717536089669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-365893055162534339642436631100823500000000000)
      constant := (2846529743747716038975617198106037820119804379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282627727852878385451/100000000000000000000)
  centralHi := (70656931963219596363/25000000000000000000)
  directionLo := (17938113400717066383/6250000000000000000)
  directionHi := (287009814411473062129/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree034.table
  base := (-5856903190393729763330091274411445922287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-375943117675560884773855119157298500000000000)
      constant := (3012090468869211162296042883540333385004701617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree034.table
  base := (-5880159898905344976071745109633569604019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-3392951744238178572301888518702249000000000000)
      constant := (27261483291234823898902095404337375536112067061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17938113400717066383/6250000000000000000)
  centralHi := (287009814411473062129/100000000000000000000)
  directionLo := (145662996833217505159/50000000000000000000)
  directionHi := (291325993666435010319/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree035.table
  base := (-5449737021261062230813157044361584006759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-387013773686032887774970831813304750000000000)
      constant := (3199225329675749424626984071105307901002279569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree035.table
  base := (-2735686893789547183886128675686129787099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-1746432996006774043910923678748543250000000000)
      constant := (14477535039277635150637787464190843527092419581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145662996833217505159/50000000000000000000)
  centralHi := (291325993666435010319/100000000000000000000)
  directionLo := (147789576427909195483/50000000000000000000)
  directionHi := (295579152855818390967/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree036.table
  base := (-501253602182696485723012403123490930753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9409000000000000000000000000000000000000000
      center := (75272)
      previous := (37636)
      next := (37636)
      square := (1151971714934800446378249147980000000000000)
      linear := (-39808442969650489077608654446931100000000000)
      constant := (339196233827779068069210512716742783207545023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree036.table
  base := (-5032649253267710493710123002606378533843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-399197804420990844815756244032436000000000000)
      constant := (3411037322122472752733448131645288209375071213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147789576427909195483/50000000000000000000)
  centralHi := (295579152855818390967/100000000000000000000)
  directionLo := (149885987187087284759/50000000000000000000)
  directionHi := (299771974374174569519/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree037.table
  base := (-7275766770408932238177128268969377619/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-81831017141395378755440451425063450000000000)
      constant := (718056433643697448025464046547879155982228625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree037.table
  base := (-2283018390742610136586876575532308893813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-1846347243782143559430882517543380750000000000)
      constant := (16247053557855982002663104117147571359156771347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149885987187087284759/50000000000000000000)
  centralHi := (299771974374174569519/100000000000000000000)
  directionLo := (60781391111891572537/20000000000000000000)
  directionHi := (151953477779728931343/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree038.table
  base := (-2028024142181254816128778555392764324977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-210112870858724448389158984890661750000000000)
      constant := (1897083675213957964368397720673342601560041407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree038.table
  base := (-81467784880494071867353100803525233787/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10367745434413204017404242331820000000000000)
      linear := (-379260873533965663438172387388159900000000000)
      constant := (3433922682534808819552273519896349832763415265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60781391111891572537/20000000000000000000)
  centralHi := (151953477779728931343/50000000000000000000)
  directionLo := (307986426088303147857/100000000000000000000)
  directionHi := (153993213044151573929/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree039.table
  base := (-3540296383976942152333126006756415985297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-431296397727920899779433682437329750000000000)
      constant := (4003602094688600088111249547187633223791215527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree039.table
  base := (-3556380946635187110197542226704824837593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-432502553679447349989075856964048500000000000)
      constant := (4026061471791721557660206927679152170290587463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307986426088303147857/100000000000000000000)
  centralHi := (153993213044151573929/50000000000000000000)
  directionLo := (78003140830944004429/25000000000000000000)
  directionHi := (312012563323776017717/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree040.table
  base := (-375201931620000797658248610927983747641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-55295881717299112847568674386667000000000000)
      constant := (527321516034461454012081789871718366543445831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree040.table
  base := (-3016524839360282542791811978271240902447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-3992437230890395665421641551471274000000000000)
      constant := (38179958259921538391596077875722348049139885593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78003140830944004429/25000000000000000000)
  centralHi := (312012563323776017717/100000000000000000000)
  directionLo := (315987405902673375641/100000000000000000000)
  directionHi := (157993702951336687821/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree041.table
  base := (-2441376633401154186885261743016135947219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-453437709748864905781665107749342250000000000)
      constant := (4439064550113270908068605604352968768669491429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree041.table
  base := (-306898508425595238527000943660885082489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-511543934833220647617700048783263937500000000)
      constant := (5021915761939142001788531813808325956540686491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315987405902673375641/100000000000000000000)
  centralHi := (157993702951336687821/50000000000000000000)
  directionLo := (19994554112691416649/6250000000000000000)
  directionHi := (63982573160612533277/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree042.table
  base := (-930409648589518352965006949642430617587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-232254182879668454391390410202674250000000000)
      constant := (2332533849475665843740762750019650741412873917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree042.table
  base := (-936803011440789620379529802601474423907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-232903651468951927581197734947830500000000000)
      constant := (2345586229925598323694487295314673649020459037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994554112691416649/6250000000000000000)
  centralHi := (63982573160612533277/20000000000000000000)
  directionLo := (323790739094798546589/100000000000000000000)
  directionHi := (32379073909479854659/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree043.table
  base := (-50442548383457678502452141668526047551/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-95115804353961782356779306612270950000000000)
      constant := (979314206842746825563216521913106907327338205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree043.table
  base := (-10183160337109118965109747772976051351/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-858435994843300842396303613571157300000000000)
      constant := (8863108371377232571381091795198500173326149225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323790739094798546589/100000000000000000000)
  centralHi := (32379073909479854659/10000000000000000000)
  directionLo := (65524543108909481489/20000000000000000000)
  directionHi := (163811357772273703723/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree044.table
  base := (-321561237909382776328013130663680332131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-243324838890140457392506122858680500000000000)
      constant := (2566782514149097375955335611157850478629979421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree044.table
  base := (-654063879312688695902554286787682830887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-4392094221991873727501476906650624000000000000)
      constant := (46460209827880261410810751204575141355197657953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65524543108909481489/20000000000000000000)
  centralHi := (163811357772273703723/50000000000000000000)
  directionLo := (33141038722105700917/10000000000000000000)
  directionHi := (331410387221057009171/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree045.table
  base := (-3955443682085443586973631107253041759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-248860166895376458893063979186683625000000000)
      constant := (2688020534613550715115785453742273003591027069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree045.table
  base := (-9012037054888753710033135663098039683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-249556026098180180167857541413636750000000000)
      constant := (2703026603419400962028557107661677687888372653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33141038722105700917/10000000000000000000)
  centralHi := (331410387221057009171/100000000000000000000)
  directionLo := (67031051244997931477/20000000000000000000)
  directionHi := (167577628112494828693/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree046.table
  base := (321871862973423384604951207805800820901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-254395494900612460393621835514686750000000000)
      constant := (2811995686327039516416727149008289869767607509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree046.table
  base := (63440067959050847831241634152160972463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10367745434413204017404242331820000000000000)
      linear := (-459192271754261275854139458424029900000000000)
      constant := (5089827920667161341829716352019760402684139303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67031051244997931477/20000000000000000000)
  centralHi := (167577628112494828693/50000000000000000000)
  directionLo := (169429370824885310091/50000000000000000000)
  directionHi := (338858741649770620183/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree047.table
  base := (262218708531163942242459368354691665233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-103972329162339384757671876737075950000000000)
      constant := (1175481780465404967415462304226576043487552297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree047.table
  base := (325616516999744621450559732483327128087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-1172959241329495568515338355758784125000000000)
      constant := (13297886958502866813025166116351703356955410247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169429370824885310091/50000000000000000000)
  centralHi := (338858741649770620183/100000000000000000000)
  directionLo := (342522185864935632977/100000000000000000000)
  directionHi := (171261092932467816489/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree048.table
  base := (996731304386155707575621605766391963673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-265466150911084463394737548170693000000000000)
      constant := (3068143649097421412855909353266832481986199257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree048.table
  base := (79419980301227246226822447289818854863/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-106483360290963373101806939151777200000000000)
      constant := (1234093950855960478930243804380130128027029835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342522185864935632977/100000000000000000000)
  centralHi := (171261092932467816489/50000000000000000000)
  directionLo := (173073430100435284183/50000000000000000000)
  directionHi := (346146860200870568367/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree049.table
  base := (538047986235134057148671617356992211009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-108400591566528185958118161799478450000000000)
      constant := (1280124162284652157575390899889961526822758681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree049.table
  base := (2682893232140909077520146174928784503913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-4891665460868721305101271100624811500000000000)
      constant := (57926267603955444449358235295373345205263356753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173073430100435284183/50000000000000000000)
  centralHi := (346146860200870568367/100000000000000000000)
  directionLo := (349733970103203664437/100000000000000000000)
  directionHi := (174866985051601832219/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree050.table
  base := (3400873234752410571913185455506084230129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-553073613843112932791706521653398500000000000)
      constant := (6670404245655735936140849934264175301208783761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree050.table
  base := (3394098046835307529448296667007856089347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-4991579708644090820621229939419649000000000000)
      constant := (60367620773941818992387014455146244605251993307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349733970103203664437/100000000000000000000)
  centralHi := (174866985051601832219/50000000000000000000)
  directionLo := (353284659816097981813/100000000000000000000)
  directionHi := (176642329908048990907/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree051.table
  base := (4124863319482298987686331569868331533977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-564144269853584935792822234309404750000000000)
      constant := (6945632903919277895515771940203455988825064593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree051.table
  base := (4118617683154119797274403394184185675423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-565721550713273370682354308690498500000000000)
      constant := (6984249474885322724737086722590499182707555007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353284659816097981813/100000000000000000000)
  centralHi := (176642329908048990907/50000000000000000000)
  directionLo := (17840000832301241629/5000000000000000000)
  directionHi := (356800016646024832581/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree052.table
  base := (151929967494277796835341365517669257299/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-71901865733007117349242243370676375000000000)
      constant := (903287817579087667158086490839996355636455164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree052.table
  base := (2428001849309065105843871965189553542313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-2595704102097414925830573808504662000000000000)
      constant := (32699051564738059289002816077057660896016607153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17840000832301241629/5000000000000000000)
  centralHi := (356800016646024832581/100000000000000000000)
  directionLo := (360281074851054477561/100000000000000000000)
  directionHi := (180140537425527238781/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree053.table
  base := (350697018389712590215986373287597290099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-73285697734316117724381707452677156250000000)
      constant := (939051164778369654517837310310349070014067357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree053.table
  base := (1401462716928696730264764078156746062171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-1322830612992549841795276613951040375000000000)
      constant := (16996790006391208188788687968815709755087577451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360281074851054477561/100000000000000000000)
  centralHi := (180140537425527238781/50000000000000000000)
  directionLo := (72745763839019146191/20000000000000000000)
  directionHi := (90932204798773932739/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree054.table
  base := (3186337328935649506506043403390460711447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-298678118942500472398084686138711750000000000)
      constant := (3901974883967158178362166531979179778427754823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree054.table
  base := (795974127131868735900312835817595322531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-74878287496466234481959240202763875000000000)
      constant := (980908124365351128979271176825134641108444179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72745763839019146191/20000000000000000000)
  centralHi := (90932204798773932739/25000000000000000000)
  directionLo := (367144188201701161267/100000000000000000000)
  directionHi := (91786047050425290317/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree055.table
  base := (1429198563125996888996232147658028350263/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-121685378779094589559457016986685950000000000)
      constant := (1620184150869154725732599666983575769606999567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree055.table
  base := (1785374815473934185005842775401694810383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 211702500000000000000000000000000000000000000
      center := (1693620)
      previous := (846810)
      next := (846810)
      square := (25919363586033010043510605829550000000000000)
      linear := (-1372787736880234599555256033348459125000000000)
      constant := (18328187474011638037520490104968609931909917823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367144188201701161267/100000000000000000000)
  centralHi := (91786047050425290317/25000000000000000000)
  directionLo := (370528077137905547557/100000000000000000000)
  directionHi := (185264038568952773779/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree056.table
  base := (7930805557309973726911328011400009870813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-619497549905944950798400797589436000000000000)
      constant := (8403319443374543288885536478175694317874479517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree056.table
  base := (7926670605349998522931854758256994582997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-5591065195296307913740982972188674000000000000)
      constant := (76049229531433244685085077511062854558282768957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370528077137905547557/100000000000000000000)
  centralHi := (185264038568952773779/50000000000000000000)
  directionLo := (23367583797186227977/6250000000000000000)
  directionHi := (373881340754979647633/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree057.table
  base := (87268406199386196466342892687944337493/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4704500000000000000000000000000000000000000
      center := (37636)
      previous := (18818)
      next := (18818)
      square := (575985857467400223189124573990000000000000)
      linear := (-31528410295820847689975825512272112500000000)
      constant := (435557163664915784988632798253940942822201935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree057.table
  base := (872303686533047038163299792969971857449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9409000000000000000000000000000000000000000
      center := (75272)
      previous := (37636)
      next := (37636)
      square := (1151971714934800446378249147980000000000000)
      linear := (-63233104923018638102899353455372350000000000)
      constant := (875942233124178080182114720656383239425487641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23367583797186227977/6250000000000000000)
  centralHi := (373881340754979647633/100000000000000000000)
  directionLo := (188602397904936992579/50000000000000000000)
  directionHi := (377204795809873985159/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree058.table
  base := (9533851905876687535770195587177039735981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-641638861926888956800632222901448500000000000)
      constant := (9024389928584403302329570797107956884063345229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree058.table
  base := (1191294237205616393474585362067918503497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-723861711355880868097612581222293625000000000)
      constant := (10208680446362569782905292470664193793513379457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188602397904936992579/50000000000000000000)
  centralHi := (377204795809873985159/100000000000000000000)
  directionLo := (38049922338842723093/10000000000000000000)
  directionHi := (380499223388427230931/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree059.table
  base := (10351616968268039522106153161854184154731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-652709517937360959801747935557454750000000000)
      constant := (9343057316230336695316629856454745907383738979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree059.table
  base := (16169376697972490569159299103443169643/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2591936358603301004351060582955000000000000)
      linear := (-147270198465560411507521487214329662500000000)
      constant := (2113828465466449436689746878142164092831309628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38049922338842723093/10000000000000000000)
  centralHi := (380499223388427230931/100000000000000000000)
  directionLo := (383765371049061394849/100000000000000000000)
  directionHi := (7675307420981227897/2000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree060.table
  base := (11179934738142222436140743090907733057667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-663780173947832962802863648213461000000000000)
      constant := (9667143544378172884861994292671038204089588803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree060.table
  base := (11176979078040721420763880372471001055163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-665635798488642886202313147485336000000000000)
      constant := (9720652138101452952377142998138817773928028667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383765371049061394849/100000000000000000000)
  centralHi := (7675307420981227897/2000000000000000000)
  directionLo := (387003954803631549809/100000000000000000000)
  directionHi := (38700395480363154981/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree061.table
  base := (12018623469946792472601530618471154723441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-674850829958304965803979360869467250000000000)
      constant := (9996646902984008927201855767138885577214731369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree061.table
  base := (600795386468569033543286549533530096249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42340500000000000000000000000000000000000000
      center := (338724)
      previous := (169362)
      next := (169362)
      square := (5183872717206602008702121165910000000000000)
      linear := (-304531821708657774567038858308143075000000000)
      constant := (4523381009451836016234323293218206349189836569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387003954803631549809/100000000000000000000)
  centralHi := (38700395480363154981/10000000000000000000)
  directionLo := (390215660950299139629/100000000000000000000)
  directionHi := (39021566095029913963/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree062.table
  base := (6433759442258986551333192541386210249473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-342960742984388484402547536762736750000000000)
      constant := (5165782923172596424488263426230837504581041457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree062.table
  base := (12865024259082869402666742347142265193497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-6190550681948525006860736004957699000000000000)
      constant := (93498377672519265100192343432407588252600519457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390215660950299139629/100000000000000000000)
  centralHi := (39021566095029913963/10000000000000000000)
  directionLo := (393401147771719565887/100000000000000000000)
  directionHi := (6146892933933118217/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree063.table
  base := (6863236245257766850449126762322393601789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-348496070989624485903105393090739875000000000)
      constant := (5335949488653352210115635158673303306672670201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree063.table
  base := (13724181573173733214121249590474314619107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-698940547747099391375632760416948500000000000)
      constant := (10730903248588174859743587860233039068438677763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393401147771719565887/100000000000000000000)
  centralHi := (6146892933933118217/1562500000000000000)
  directionLo := (396561047110446610343/100000000000000000000)
  directionHi := (49570130888805826293/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree064.table
  base := (2919070013434241116578982529182497980593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-141612559597944194961465299767497200000000000)
      constant := (2203529006597067000182909128556228923499399537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree064.table
  base := (364831168835497884381621263287832757063/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2591936358603301004351060582955000000000000)
      linear := (-159759479437481600947516342063684350000000000)
      constant := (2492671590692787872230904806291342865700851903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396561047110446610343/100000000000000000000)
  centralHi := (49570130888805826293/12500000000000000000)
  directionLo := (399695965832232759357/100000000000000000000)
  directionHi := (199847982916116379679/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree065.table
  base := (15474030292848149600188984033648636682999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-719133454000192977808442211493492250000000000)
      constant := (11368802871865803571478423265278059895597212591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree065.table
  base := (15472099691238277681253274712189149351663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-6490293425274633553420612521342211500000000000)
      constant := (102884570672858159828499630294416842910935674503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399695965832232759357/100000000000000000000)
  centralHi := (199847982916116379679/50000000000000000000)
  directionLo := (40280648718682386549/10000000000000000000)
  directionHi := (402806487186823865491/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree066.table
  base := (2045300438174849340892270170649409099233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-91275513751333122601194740518687312500000000)
      constant := (1465671432767120454517829340580932968925620797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree066.table
  base := (654425274128221457916611261359683420207/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-146449059401111179309790474669712200000000000)
      constant := (2358027581822548699329406667672540725253638315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40280648718682386549/10000000000000000000)
  centralHi := (402806487186823865491/100000000000000000000)
  directionLo := (202946586037445096787/50000000000000000000)
  directionHi := (16235726882995607743/4000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree067.table
  base := (8630185290827500778061719114521120188271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-370637383010568491905336818402752375000000000)
      constant := (6043674935574463085610446394781728554812379339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree067.table
  base := (8629372582772479926142488871399079357363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-3345060960412686292230265099465943250000000000)
      constant := (54693433425097811192853313348771856372654606203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202946586037445096787/50000000000000000000)
  centralHi := (16235726882995607743/4000000000000000000)
  directionLo := (408956560228887808913/100000000000000000000)
  directionHi := (204478280114443904457/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree068.table
  base := (145342735396813815247069281037165763463/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-150469084406321797362357869892302200000000000)
      constant := (2490947451176675327084142251475493635460584175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree068.table
  base := (2270793875764484743990202778375341312731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-848754521075092762497561129715840500000000000)
      constant := (14088930021598682313094223231647898855828373811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408956560228887808913/100000000000000000000)
  centralHi := (204478280114443904457/50000000000000000000)
  directionLo := (51499646414361347701/12500000000000000000)
  directionHi := (411997171314890781609/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree069.table
  base := (3816947309577122456693757014534668331653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-152683215608416197962581012423503450000000000)
      constant := (2565506570867943255736384636592964734566898077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree069.table
  base := (4770842323386482729922987816053089637727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-191387511566003100430567996570043375000000000)
      constant := (3224582065789597417345647377969632440323248343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51499646414361347701/12500000000000000000)
  centralHi := (411997171314890781609/100000000000000000000)
  directionLo := (83003101192352803563/20000000000000000000)
  directionHi := (51876938245220502227/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree070.table
  base := (20010981248304431047239319558252806609867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-774486734052552992814020774773523500000000000)
      constant := (13205735977749015350533342571985225149579738603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree070.table
  base := (20009727664144379447293349587005798469803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-6989864664151481131020406715316399000000000000)
      constant := (119507403309274072449408812195253945363971387843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83003101192352803563/20000000000000000000)
  centralHi := (51876938245220502227/12500000000000000000)
  directionLo := (418012046723448517573/100000000000000000000)
  directionHi := (209006023361724258787/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree071.table
  base := (4189301971564453570179006605366781513177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-157111478012604999163027297485905950000000000)
      constant := (2717869200707244784696326111020772940616857393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree071.table
  base := (2618170091017123098395623757676289024673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-886222363990856330817545694263904562500000000)
      constant := (15372347682257960308533513401961597243984271813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418012046723448517573/100000000000000000000)
  centralHi := (209006023361724258787/50000000000000000000)
  directionLo := (210493629489798353409/50000000000000000000)
  directionHi := (420987258979596706819/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree072.table
  base := (10945631283733926950384695692398082763541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-398314023036748499408126100042768000000000000)
      constant := (6989181184479365664723589356516933623222157269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree072.table
  base := (10945104698789103297861578993983435565303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-399427397761234453447795799605893000000000000)
      constant := (7027726878398223376621454340208798645233935927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210493629489798353409/50000000000000000000)
  centralHi := (420987258979596706819/100000000000000000000)
  directionLo := (6624087371551837159/1562500000000000000)
  directionHi := (423941591779317578177/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree073.table
  base := (22845185316207944698399741970772405823309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-807698702083969001817367912741542250000000000)
      constant := (14372784565356275770943951946884429033188389381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree073.table
  base := (11422110139516571582708875982073673239613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-3644803703738794838790141615850455750000000000)
      constant := (65034152923588813235332987391291626938447418453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6624087371551837159/1562500000000000000)
  centralHi := (423941591779317578177/100000000000000000000)
  directionLo := (21343773931618154153/5000000000000000000)
  directionHi := (426875478632363083061/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree074.table
  base := (952329169542060297054001062799956909221/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-163753871618888200963696725079509700000000000)
      constant := (2954522426590690424038538876982567671231801945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree074.table
  base := (2975918140598415240577625880057418935159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-923690206906619899137530258811968625000000000)
      constant := (16710805435053473786358685803559930992066949279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21343773931618154153/5000000000000000000)
  centralHi := (426875478632363083061/100000000000000000000)
  directionLo := (53723667281462848399/12500000000000000000)
  directionHi := (429789338251702787193/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree075.table
  base := (2478035016524056598372127443726843930351/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9409000000000000000000000000000000000000000
      center := (75272)
      previous := (37636)
      next := (37636)
      square := (1151971714934800446378249147980000000000000)
      linear := (-82984001410491300781959933805355475000000000)
      constant := (1517784465616171208006004761137743994657860059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree075.table
  base := (4955908067388795953371218394806872141599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-166431908956185082413782242428679700000000000)
      constant := (3052299844866778143181714411443769070917804991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53723667281462848399/12500000000000000000)
  centralHi := (429789338251702787193/100000000000000000000)
  directionLo := (216341787625544105229/50000000000000000000)
  directionHi := (432683575251088210459/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree076.table
  base := (25761508171925964062283573849309848338129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-840910670115385010820715050709561000000000000)
      constant := (15588481759332854438841876386873975956763455761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree076.table
  base := (25760766519312035066139973964551081889277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-7589350150803698224140159748085424000000000000)
      constant := (141069451126800447944419091841489727290465865637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216341787625544105229/50000000000000000000)
  centralHi := (432683575251088210459/100000000000000000000)
  directionLo := (217779290400448565969/50000000000000000000)
  directionHi := (435558580800897131939/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree077.table
  base := (5350333434243318509175518873347958599441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18818000000000000000000000000000000000000000
      center := (150544)
      previous := (75272)
      next := (75272)
      square := (2303943429869600892756498295960000000000000)
      linear := (-170396265225171402764366152673113450000000000)
      constant := (3200904620584123250172847514259657676446515369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree077.table
  base := (13375494036239566298525181774592061806387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-3844632199289533869830059293440130750000000000)
      constant := (72417157394610123570875665757019144131920407547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217779290400448565969/50000000000000000000)
  centralHi := (435558580800897131939/100000000000000000000)
  directionLo := (219207366622633805357/50000000000000000000)
  directionHi := (87682946649053522143/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree078.table
  base := (693769863598344907611973507207581430717/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2352250000000000000000000000000000000000000
      center := (18818)
      previous := (9409)
      next := (9409)
      square := (287992928733700111594562286995000000000000)
      linear := (-21576299553408225420573661900539337500000000)
      constant := (410649209500278638750218290637431719423803753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree078.table
  base := (6937543206976996776067194635660059590557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-216366073509845479310557706268752750000000000)
      constant := (4129113368950014116179673420630068711625050813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219207366622633805357/50000000000000000000)
  centralHi := (87682946649053522143/20000000000000000000)
  directionLo := (110313099670819545961/25000000000000000000)
  directionHi := (88250479736655636769/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree079.table
  base := (575177216116065102571669870189554306773/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9409000000000000000000000000000000000000000
      center := (75272)
      previous := (37636)
      next := (37636)
      square := (1151971714934800446378249147980000000000000)
      linear := (-87412263814680101982406218867757975000000000)
      constant := (1685281731318690525742413430222546469666823285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree079.table
  base := (28758291717295322578009923395043039139747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-7889092894129806770700036264469936500000000000)
      constant := (152510748144208241350785198114963201027080415707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110313099670819545961/25000000000000000000)
  centralHi := (88250479736655636769/20000000000000000000)
  directionLo := (111017982879175423769/25000000000000000000)
  directionHi := (444071931516701695077/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree080.table
  base := (7443959826544679239599506926909600086869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-221298323539318255706294475333396500000000000)
      constant := (4321267412922991196869962783753324927217350421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree080.table
  base := (5955063694759024882765235677216734857719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-1597801428381035257243999020652954800000000000)
      constant := (31284462630188131856796593509068999324486502639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111017982879175423769/25000000000000000000)
  centralHi := (444071931516701695077/100000000000000000000)
  directionLo := (223436837483326438257/50000000000000000000)
  directionHi := (89374734993330575303/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree081.table
  base := (30801705955719248231609760381098179128847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-896263950167745025826293613989592250000000000)
      constant := (17722725168869715296288081153302399577970196423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree081.table
  base := (15400614681017707679508912667681510943391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-449384521648919211207775219003311750000000000)
      constant := (8910154127359040420906982588810749020060115919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223436837483326438257/50000000000000000000)
  centralHi := (89374734993330575303/20000000000000000000)
  directionLo := (449657961561261854277/100000000000000000000)
  directionHi := (224828980780630927139/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree082.table
  base := (15918219490118750051969479214495727367241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-453667303089108514413704663322799250000000000)
      constant := (9082891829923414009286498174173359951142120569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree082.table
  base := (31836002934153699311238951241407714771237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-8188835637455915317259912780854449000000000000)
      constant := (164392129752548002195370601015830892038293120397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449657961561261854277/100000000000000000000)
  centralHi := (224828980780630927139/50000000000000000000)
  directionLo := (90485022719267030043/20000000000000000000)
  directionHi := (56553139199541893777/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree083.table
  base := (3288001869820389312936265448009401228317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9409000000000000000000000000000000000000000
      center := (75272)
      previous := (37636)
      next := (37636)
      square := (1151971714934800446378249147980000000000000)
      linear := (-91840526218868903182852503930160475000000000)
      constant := (1861424493943979114132696662015041204399422153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree083.table
  base := (16439809904671815557002698860308228800603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-4144374942615642416389935809824643250000000000)
      constant := (84225188945005210513460737890487742181657612643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90485022719267030043/20000000000000000000)
  centralHi := (56553139199541893777/12500000000000000000)
  directionLo := (455175443570810711547/100000000000000000000)
  directionHi := (113793860892702677887/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree084.table
  base := (33932427319633328885816253326726274666019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-929475918199161034829640751957611000000000000)
      constant := (19068108840262634873496786192404418862082572771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree084.table
  base := (16966031237323556930525058097494977052041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-466036896278147463794435025469118000000000000)
      constant := (9586528734546398859269928386299650051582653769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455175443570810711547/100000000000000000000)
  centralHi := (113793860892702677887/25000000000000000000)
  directionLo := (457909254598672429849/100000000000000000000)
  directionHi := (9158185091973448597/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree085.table
  base := (4374206095537439324861481020055454963827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-117568321776204129728844558076702156250000000)
      constant := (2440921901377063753296006383743510636838632618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree085.table
  base := (17496657552472190695624986759475215629091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-4244289190391011931909894648619480750000000000)
      constant := (88356773203967655298446119247592435168280804971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457909254598672429849/100000000000000000000)
  centralHi := (9158185091973448597/2000000000000000000)
  directionLo := (460626840798861100589/100000000000000000000)
  directionHi := (46062684079886110059/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree086.table
  base := (36063668497419468321855212468961799734837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-951617230220105040831872177269623500000000000)
      constant := (19992043914943643522803938915527327690892581333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree086.table
  base := (901584085007298420212753398977111195843/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21170250000000000000000000000000000000000000
      center := (169362)
      previous := (84681)
      next := (84681)
      square := (2591936358603301004351060582955000000000000)
      linear := (-214712315713934834483493703400844975000000000)
      constant := (4522961605934432478909096294774245224268931083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460626840798861100589/100000000000000000000)
  centralHi := (46062684079886110059/10000000000000000000)
  directionLo := (231664243832300785903/50000000000000000000)
  directionHi := (463328487664601571807/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree087.table
  base := (37142473381129275423631772073019230181377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-962687886230577043832987889925629750000000000)
      constant := (20462114828429873790040669060689474966073451193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree087.table
  base := (37142194438936515907030990085597098652501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-965378541814751432762189663869848500000000000)
      constant := (20574696623992684108784692641766672718408881909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231664243832300785903/50000000000000000000)
  centralHi := (463328487664601571807/100000000000000000000)
  directionLo := (116503618103364705227/25000000000000000000)
  directionHi := (466014472413458820909/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree088.table
  base := (38230051540233515858475204825127663970169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-973758542241049046834103602581636000000000000)
      constant := (20937587839741487120867814360348809815295320121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree088.table
  base := (1194681142015448743876024014807162744773/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-1098540140513516551297458226702934250000000000)
      constant := (23684370194354753872379338870586005393560489652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116503618103364705227/25000000000000000000)
  centralHi := (466014472413458820909/100000000000000000000)
  directionLo := (234342532159668944469/50000000000000000000)
  directionHi := (468685064319337888939/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree089.table
  base := (9831598060214156127579679305419690975759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23522500000000000000000000000000000000000000
      center := (188180)
      previous := (94090)
      next := (94090)
      square := (2879929287337001115945622869950000000000000)
      linear := (-246207299562880262458804828809410562500000000)
      constant := (5354615711970862080777075588607470348465135181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree089.table
  base := (1228942473935333430199851883224290467771/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-1111029421485437740737453081552288937500000000)
      constant := (24228317395077092920595241347680876461866201704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234342532159668944469/50000000000000000000)
  centralHi := (468685064319337888939/100000000000000000000)
  directionLo := (47134052502755310553/10000000000000000000)
  directionHi := (471340525027553105531/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree090.table
  base := (5053935722594534245103848406695199141599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11761250000000000000000000000000000000000000
      center := (94090)
      previous := (47045)
      next := (47045)
      square := (1439964643668500557972811434975000000000000)
      linear := (-124487481782749131604541878486706062500000000)
      constant := (2738092470195919917260381469043620612121742491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree090.table
  base := (40431272769105675475032765512606816786059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-998683291073207937935509276801461000000000000)
      constant := (22025222402878867138428155229941134882890029131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47134052502755310553/10000000000000000000)
  centralHi := (471340525027553105531/100000000000000000000)
  directionLo := (236990554427005031731/50000000000000000000)
  directionHi := (473981108854010063463/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree091.table
  base := (20772661695089013629282741896300747385311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-503485255136232527918725370274827375000000000)
      constant := (11198209249139300334257953894060532488984328699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree091.table
  base := (20772564369386313956388275392892386971671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 423405000000000000000000000000000000000000000
      center := (3387240)
      previous := (1693620)
      next := (1693620)
      square := (51838727172066020087021211659100000000000000)
      linear := (-4544031933717120478469771165003993250000000000)
      constant := (101338174110584751834393122156317767592241821951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236990554427005031731/50000000000000000000)
  centralHi := (473981108854010063463/100000000000000000000)
  directionLo := (119151765767367160139/25000000000000000000)
  directionHi := (476607063069468640557/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree092.table
  base := (42667897142238215160978483537538807767577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-1018041166282937058838566453205661000000000000)
      constant := (22893498983433123870503770923804629486035131993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree092.table
  base := (2666732455626278218582085756975424723743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 105851250000000000000000000000000000000000000
      center := (846810)
      previous := (423405)
      next := (423405)
      square := (12959681793016505021755302914775000000000000)
      linear := (-1148497264401201309057437646100353000000000000)
      constant := (25896822285895223355271825587278235772687561966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119151765767367160139/25000000000000000000)
  centralHi := (476607063069468640557/100000000000000000000)
  directionLo := (479218628169786384003/100000000000000000000)
  directionHi := (119804657042446596001/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree093.table
  base := (43799199871919348372631388655651667030433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-1029111822293409061839682165861667250000000000)
      constant := (23395981149615279387265861274191578392511219097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree093.table
  base := (21899518694125430537149364332702783856933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-515994020165832221554414444866536750000000000)
      constant := (11762316179343879798936857308439311895653632597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479218628169786384003/100000000000000000000)
  centralHi := (119804657042446596001/25000000000000000000)
  directionLo := (481816038132978198541/100000000000000000000)
  directionHi := (240908019066489099271/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree094.table
  base := (22469612551425187622145046396903174771609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-520091239151940532420398939258836750000000000)
      constant := (11951932467944445996917267566302638248769819081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree094.table
  base := (44939076676867465602835355208251075871463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 846810000000000000000000000000000000000000000
      center := (6774480)
      previous := (3387240)
      next := (3387240)
      square := (103677454344132040174042423318200000000000000)
      linear := (-9387806610760349503499418846392499000000000000)
      constant := (216317686505970713295118503555982886449621358303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481816038132978198541/100000000000000000000)
  centralHi := (240908019066489099271/50000000000000000000)
  directionLo := (15137485020745937627/3125000000000000000)
  directionHi := (96879904132774000813/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree095.table
  base := (46087966981123638366465608628077379980367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-1051253134314353067841913591173679750000000000)
      constant := (24417150287174544541643910617314909003782148103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree095.table
  base := (9217566282386728665407693953512450644407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 169362000000000000000000000000000000000000000
      center := (1354896)
      previous := (677448)
      next := (677448)
      square := (20735490868826408034808484663640000000000000)
      linear := (-1897544171707143803803875537037467300000000000)
      constant := (44192512726820424103605948297646313168956529167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15137485020745937627/3125000000000000000)
  centralHi := (96879904132774000813/20000000000000000000)
  directionLo := (486969297427070390233/100000000000000000000)
  directionHi := (243484648713535195117/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree096.table
  base := (47245420215472282216597808952376121516717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (752720)
      previous := (376360)
      next := (376360)
      square := (11519717149348004463782491479800000000000000)
      linear := (-1062323790324825070843029303829686000000000000)
      constant := (24935837153686707187082219491438387927350790253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree096.table
  base := (23622648201563798787501442652040915180619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-532646394795060474141074251332343000000000000)
      constant := (12536462342947912110312419011387905970934444171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486969297427070390233/100000000000000000000)
  centralHi := (243484648713535195117/50000000000000000000)
  directionLo := (48952558426893488169/10000000000000000000)
  directionHi := (489525584268934881691/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree097.table
  base := (12102895005799213281630599269972482488781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (20)
      previous := (10)
      next := (10)
      square := (306082398484111076197855550000000000000)
      linear := (-28520417853525801728242773315062500000000)
      constant := (676477986247873333260327980854753244207531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree097.table
  base := (24205733480193862097447704005522408174411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (360)
      previous := (180)
      next := (180)
      square := (5509483172713999371561399900000000000000)
      linear := (-514802282606358701778047367561750000000000)
      constant := (12243541381958364278707541663379979017319699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell043.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48952558426893488169/10000000000000000000)
  centralHi := (489525584268934881691/100000000000000000000)
  directionLo := (492068591429151864363/100000000000000000000)
  directionHi := (123017147857287966091/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2983
  qDenominator := 6208
  table := BinomialMassData.Q2983_6208.Degree098.table
  base := (24793221040644288176298248775533979790827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (376360)
      previous := (188180)
      next := (188180)
      square := (5759858574674002231891245739900000000000000)
      linear := (-542232551172884538422630364570849250000000000)
      constant := (12994707628357057865295713995074655305695641243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2983_6208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4487
  qDenominator := 9312
  table := BinomialMassData.Q4487_9312.Degree098.table
  base := (991726776913998124413524954123543720139/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84681000000000000000000000000000000000000000
      center := (677448)
      previous := (338724)
      next := (338724)
      square := (10367745434413204017404242331820000000000000)
      linear := (-978746360186182756557925420157184900000000000)
      constant := (23519048193311309011251345646531283213200453295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4487_9312.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell043.Kernel098
