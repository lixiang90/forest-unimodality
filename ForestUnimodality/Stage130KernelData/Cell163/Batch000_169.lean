import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell163.Parameters
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95549_180624.Batch150_199
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch000_049
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch050_099
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch100_149
import ForestUnimodality.BinomialMassData.Q15929_30104.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree000.table
  base := (679314658353291511050287003/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (185525840646925781196596717500000000000)
      linear := (-14165428974649322494544501000000000000)
      constant := (169828664588322877762571750750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree000.table
  base := (679314658353291511050287003/10000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (185525840646925781196596717500000000000)
      linear := (-14165428974649322494544501000000000000)
      constant := (169828664588322877762571750750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree001.table
  base := (380541518051438603461236580221200869690781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-107280026105621348079903468376124217750000000000)
      constant := (48527075052756693030709958732951359198564367817901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree001.table
  base := (380463685625514641057493932490486789612829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-11922911791201070821578063681158048500000000000)
      constant := (5390796757817147268421378719727873304028853208101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12478764629742241649/25000000000000000000)
  directionHi := (49915058518968966597/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree002.table
  base := (227327823398988757687434071140295993960463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-207338996954655575758509875113744351500000000000)
      constant := (29084504545287265814938164456240257954621968584223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree002.table
  base := (227248320968520573582380684957990983861367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-23043484109448017154123120513593421000000000000)
      constant := (3230492226340901715769836897714625788328229291023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12478764629742241649/25000000000000000000)
  centralHi := (49915058518968966597/100000000000000000000)
  directionLo := (17647638181043152003/25000000000000000000)
  directionHi := (70590552724172608013/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree003.table
  base := (18204058256122209743493392831691105051581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-8538832438991383428808785606982346812500000000)
      constant := (522479730874100508064044471941579887941390729378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree003.table
  base := (145569323177030151251885937948087202468979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-34164056427694963486668177346028793500000000000)
      constant := (2089038993792616284202661621625606270291709897451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/25000000000000000000)
  centralHi := (70590552724172608013/100000000000000000000)
  directionLo := (43227708708813983399/50000000000000000000)
  directionHi := (86455417417627966799/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree004.table
  base := (24932627169890079931244460917192185096869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-101864234663181007778930672147246154750000000000)
      constant := (3287133000343037864287846469014117421902267697749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree004.table
  base := (4984186944290053672848330756362327745473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-11321157186485477454803308544616041500000000000)
      constant := (365077699990335317786750000574536323421433324685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/50000000000000000000)
  centralHi := (86455417417627966799/100000000000000000000)
  directionLo := (99830117037937933193/100000000000000000000)
  directionHi := (49915058518968966597/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree005.table
  base := (72244187827137837286038379855243558627379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-507515909501758258794329095326604752750000000000)
      constant := (9887641007621600281482915491270261098136789503459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree005.table
  base := (72209767547460293654936541258717094208521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-56405201064188856151758291010899538500000000000)
      constant := (1098178411571981831513550084416220278275328600049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/100000000000000000000)
  centralHi := (49915058518968966597/50000000000000000000)
  directionLo := (55806731974647292603/50000000000000000000)
  directionHi := (111613463949294585207/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree006.table
  base := (27305397557462777664282262690266158108593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-33754160019488471470718639003568049250000000000)
      constant := (440852930599949147402792760848168307345272232217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree006.table
  base := (6823112604833673947647506282170795428329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-16881443345608950621075836960833727750000000000)
      constant := (220348815925539822540582329041696811602882055202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55806731974647292603/50000000000000000000)
  centralHi := (111613463949294585207/100000000000000000000)
  directionLo := (15283302981579572087/12500000000000000000)
  directionHi := (122266423852636576697/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree007.table
  base := (425268475899938889207896327209221964767/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-176908462799956678537885477200461255062500000000)
      constant := (1685806204446421715712606427638482516231231640175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree007.table
  base := (21253368048080006134470791000371876681169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-39323172850341374408424202337885141750000000000)
      constant := (374519303766971824206044792263142438824387157561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15283302981579572087/12500000000000000000)
  centralHi := (122266423852636576697/100000000000000000000)
  directionLo := (26412566303685580969/20000000000000000000)
  directionHi := (66031415759213952423/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree008.table
  base := (54024165851649163359017538045467287263/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-807692822048860941830148315539465154000000000000)
      constant := (6027414152072225399646121053828884442337904389375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree008.table
  base := (527328122702719365522784116253893322181/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-22441729504732423787348365377051414000000000000)
      constant := (167396008633748015795632147346867666100870537424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26412566303685580969/20000000000000000000)
  centralHi := (66031415759213952423/50000000000000000000)
  directionLo := (17647638181043152003/12500000000000000000)
  directionHi := (5647244217933808641/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree009.table
  base := (6781196126304634964271037588609043142999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-25215327580497088041909853396585702437500000000)
      constant := (156524768764665606813827981693531762292141381831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree009.table
  base := (677789553086999908119738619121242819293/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-25221872584294160370484629585160257125000000000)
      constant := (156509446122543813418535270978440139698190905170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/12500000000000000000)
  centralHi := (5647244217933808641/4000000000000000000)
  directionLo := (149745175556906899789/100000000000000000000)
  directionHi := (14974517555690689979/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree010.table
  base := (438472509420516556922872654404623302479/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-503905381873464698593680564507352710750000000000)
      constant := (2739354270901734916134459385467128948671045763975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree010.table
  base := (21912632255599741968181507124880324068349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-112008062655423587814483575173076401000000000000)
      constant := (608744736933306540779363165341051862957589390981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149745175556906899789/100000000000000000000)
  centralHi := (14974517555690689979/10000000000000000000)
  directionLo := (157845274460532913511/100000000000000000000)
  directionHi := (19730659307566614189/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree011.table
  base := (17749675543112813766146730490634982535557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-1107869734595963624865967535752325555250000000000)
      constant := (5506365087404259513342952538756475659100758162197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree011.table
  base := (8870220788904447548087374381159840228561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-61564317486835267073514316002755886750000000000)
      constant := (305937513748417599348471698475192747196297386809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157845274460532913511/100000000000000000000)
  centralHi := (19730659307566614189/12500000000000000000)
  directionLo := (165549520496052964121/100000000000000000000)
  directionHi := (82774760248026482061/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree012.table
  base := (896133758401260238712440642095122627103/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-33553575151249940348460387291387380250000000000)
      constant := (157892096872303402002639690482470912245759841628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree012.table
  base := (14330354096043447222241816903388404211929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-134249207291917480479573688837947146000000000000)
      constant := (631681082577951870440218824325526695781226456001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165549520496052964121/100000000000000000000)
  centralHi := (82774760248026482061/50000000000000000000)
  directionLo := (43227708708813983399/25000000000000000000)
  directionHi := (172910834835255933597/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree013.table
  base := (2301765375067481592008314587764277712113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-1307987676294032080223180349227565822750000000000)
      constant := (5988995752143706228355934577267380678076341719365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree013.table
  base := (5751128651674654086471290932660852375607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-72684889805082213406059372835191259250000000000)
      constant := (332806239319586481956018949888304822619521597583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/25000000000000000000)
  centralHi := (172910834835255933597/100000000000000000000)
  directionLo := (35994260581585644383/20000000000000000000)
  directionHi := (44992825726982055479/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree014.table
  base := (9133280546804439288620832205394877977583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-1408046647143066307901786755965185956500000000000)
      constant := (6404635353129202568436725886861269884666331423743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree014.table
  base := (2281936005783285754214532220557516263283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-39122587982102843286165950625704472750000000000)
      constant := (177962737089781003052476345105510836602085774827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35994260581585644383/20000000000000000000)
  centralHi := (44992825726982055479/25000000000000000000)
  directionLo := (93382523709376892261/50000000000000000000)
  directionHi := (186765047418753784523/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree015.table
  base := (7116708597100593681234005483285881990041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-167567290888011170620043684744756232250000000000)
      constant := (768772642598739876584121624343710958003974376929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree015.table
  base := (3556026485856917389295249411030735032139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-83805462123329159738604429667626631750000000000)
      constant := (384527327973111728426708661348438974671183671491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382523709376892261/50000000000000000000)
  centralHi := (186765047418753784523/100000000000000000000)
  directionLo := (4833004759223386467/2500000000000000000)
  directionHi := (193320190368935458681/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree016.table
  base := (2693731814461528015016477539599491812563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-804082294420567381629499784720213112000000000000)
      constant := (3761410094817056567945547534656383724420075628323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree016.table
  base := (5383559229863385536466737971955703411043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-178731496564905265809753916167688636000000000000)
      constant := (836209380439591497740035939297835316814245346267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4833004759223386467/2500000000000000000)
  centralHi := (193320190368935458681/100000000000000000000)
  directionLo := (99830117037937933193/50000000000000000000)
  directionHi := (199660234075875866387/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree017.table
  base := (486316139903049425082818046929634525829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-427055889922542247734401494044511589437500000000)
      constant := (2052305795622067288730514368199315393241132466818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree017.table
  base := (971816001389849189759561305180745553767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-47463017220788053035574743250031002125000000000)
      constant := (228134082412348779969774305919220083048276806623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/50000000000000000000)
  centralHi := (199660234075875866387/100000000000000000000)
  directionLo := (205805058582595677863/100000000000000000000)
  directionHi := (25725632322824459733/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree018.table
  base := (2583230281195226316818633345919304916581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-200920281171022579846245820323962943500000000000)
      constant := (996969358023532013797163640669573020825067862189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree018.table
  base := (2580507450858134734460064513048694254259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-200972641201399158474844029832559381000000000000)
      constant := (997431432919236751419879296293184738244636409771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205805058582595677863/100000000000000000000)
  centralHi := (25725632322824459733/12500000000000000000)
  directionLo := (52942914543129456009/25000000000000000000)
  directionHi := (211771658172517824037/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree019.table
  base := (716127897211473876982353855493718279339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-954170750694118723147409394826643312625000000000)
      constant := (4904539031732384910757624624580794846757433784619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree019.table
  base := (714995648054924959620740747416757723139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-106046606759823052403694543332497376750000000000)
      constant := (545211590561734184009440395980988131588578450491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52942914543129456009/25000000000000000000)
  centralHi := (211771658172517824037/100000000000000000000)
  directionLo := (217574695845104725947/100000000000000000000)
  directionHi := (54393673961276181487/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree020.table
  base := (411501818380846728552118892352737842957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-2008400472237271673973425196390906759000000000000)
      constant := (10714957993106548503190499169891955343595699217597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree020.table
  base := (409623269365200961640737411248807438007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-223213785837893051139934143497430126000000000000)
      constant := (1191142103281693336696749962357651821870636143183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217574695845104725947/100000000000000000000)
  centralHi := (54393673961276181487/25000000000000000000)
  directionLo := (223226927898589170413/100000000000000000000)
  directionHi := (111613463949294585207/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree021.table
  base := (-15610509423709085869550365741927198003/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-58568317863508497268111988975792413687500000000)
      constant := (324659746298994482053245125832637121118007834944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree021.table
  base := (-4008728073285044901497434499514756069/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-234334358156139997472479200329865498500000000000)
      constant := (1299297995512608444222439279275023051602398042375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223226927898589170413/100000000000000000000)
  centralHi := (111613463949294585207/50000000000000000000)
  directionLo := (228739533981325634129/100000000000000000000)
  directionHi := (22873953398132563413/10000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree022.table
  base := (-164623555029280992978013822762999265987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-552129603483835032332659502466536756625000000000)
      constant := (3181350267163389923112900165607465284627403807546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree022.table
  base := (-1318272327604810327184413689658889724513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-245454930474386943805024257162300871000000000000)
      constant := (1414662584731778231603034507601442920523532477303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228739533981325634129/100000000000000000000)
  centralHi := (22873953398132563413/10000000000000000000)
  directionLo := (117061188564940387879/50000000000000000000)
  directionHi := (234122377129880775759/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree023.table
  base := (-1026777131009806587963786693127467228129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-1154288692392187178504622208301883580125000000000)
      constant := (6913145067115919211605026150992438878831305005791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree023.table
  base := (-2054612369579490629923002422302224218141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-256575502792633890137569313994736243500000000000)
      constant := (1537056154554360089720071883463912481338980574171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117061188564940387879/50000000000000000000)
  centralHi := (234122377129880775759/100000000000000000000)
  directionLo := (239384211133270477681/100000000000000000000)
  directionHi := (119692105566635238841/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree024.table
  base := (-1359619017927996811341104910194039177119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-133813130868522699149325045741188183000000000000)
      constant := (832730172458237613543451773064033078209374026889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree024.table
  base := (-2720108447723917375977009823851219490657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-267696075110880836470114370827171616000000000000)
      constant := (1666337141343836461233153148666659455156202958967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384211133270477681/100000000000000000000)
  centralHi := (119692105566635238841/50000000000000000000)
  directionLo := (244532847705273153393/100000000000000000000)
  directionHi := (122266423852636576697/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree025.table
  base := (-3321923256685629058992392375186471182487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-2508695326482442812366457230079007427750000000000)
      constant := (16212955294116640710107328642169808459154625657273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree025.table
  base := (-3322638038535865263643571469740715460331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-278816647429127782802659427659606988500000000000)
      constant := (1802393998701705328290466851245614260244550244061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244532847705273153393/100000000000000000000)
  centralHi := (122266423852636576697/50000000000000000000)
  directionLo := (124787646297422416491/50000000000000000000)
  directionHi := (249575292594844832983/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree026.table
  base := (-483477929467199533993804943903550796957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-652188574332869260011265909204156890375000000000)
      constant := (4374233711128786324253201061476594954231012996806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree026.table
  base := (-3868409481937516088475035333496171649241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-289937219747374729135204484492042361000000000000)
      constant := (1945138815485459149818268295548848863968738718271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124787646297422416491/50000000000000000000)
  centralHi := (249575292594844832983/100000000000000000000)
  directionLo := (254517857410348530797/100000000000000000000)
  directionHi := (127258928705174265399/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree027.table
  base := (-4361836436520434087826418908056771134859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-300979252020056807524852227061583077250000000000)
      constant := (2093384173807623579999016284422378430159512268829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree027.table
  base := (-4362316225558804868308125372527674579791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-301057792065621675467749541324477733500000000000)
      constant := (2094502299649665396504971455933087638866905455321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254517857410348530797/100000000000000000000)
  centralHi := (127258928705174265399/50000000000000000000)
  directionLo := (129683126126441950197/50000000000000000000)
  directionHi := (51873250450576780079/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree028.table
  base := (-4807823325417113929482479216550171855207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-2808872239029545495402276450291867829000000000000)
      constant := (20243031393204513632413269171165836517336028150153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree028.table
  base := (-4808215585832485941306291079855832115407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-312178364383868621800294598156913106000000000000)
      constant := (2250429830941749789786698737954194457110209376217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129683126126441950197/50000000000000000000)
  centralHi := (51873250450576780079/20000000000000000000)
  directionLo := (264125663036855809691/100000000000000000000)
  directionHi := (66031415759213952423/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree029.table
  base := (-1041765595169857039994281403751781341663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-2908931209878579723080882857029487962750000000000)
      constant := (21704268415464263060025382919792451297131170552885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree029.table
  base := (-520914826738339924417111330105238564243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-161649468351057784066419827494674239250000000000)
      constant := (1206439176235172757280903227135855279521883814665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264125663036855809691/100000000000000000000)
  centralHi := (66031415759213952423/25000000000000000000)
  directionLo := (268800816482410997431/100000000000000000000)
  directionHi := (33600102060301374679/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree030.table
  base := (-1391812522328938438859490866469483041399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-83583060575767054187763590660197447125000000000)
      constant := (645107300262191852912130340233090388627093663569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree030.table
  base := (-43496182075710668088393683322370083491/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-83604877255090628616346177955445962750000000000)
      constant := (645453480451991244288069683343706138984896560672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268800816482410997431/100000000000000000000)
  centralHi := (33600102060301374679/12500000000000000000)
  directionLo := (273396035100297115029/100000000000000000000)
  directionHi := (27339603510029711503/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree031.table
  base := (-2942490775312643895283192037502046069139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-1554524575788324089219047835252364115125000000000)
      constant := (12400786735225429176990107033970600652661073429581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree031.table
  base := (-5885194351263716465630355856255585126821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-345540081338609460797929768654219223500000000000)
      constant := (2757209781184056432589994133320480633254078207251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273396035100297115029/100000000000000000000)
  centralHi := (27339603510029711503/10000000000000000000)
  directionLo := (138957641995245253007/50000000000000000000)
  directionHi := (55583056798098101203/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree032.table
  base := (-3081756952254159633589295705173491348381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-1604554061212841203058351038621174182000000000000)
      constant := (13218605156885516111627174317857601077681984472499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree032.table
  base := (-6163687082837610987921193196463371519943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-356660653656856407130474825486654596000000000000)
      constant := (2939044836495962996575820806549452408967820249633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138957641995245253007/50000000000000000000)
  centralHi := (55583056798098101203/20000000000000000000)
  directionLo := (17647638181043152003/6250000000000000000)
  directionHi := (282362210896690432049/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree033.table
  base := (-1601005769491455142258898360625911444083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-91921308146519906494314124554999124937500000000)
      constant := (781406207707606650655377705429090173287985044973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree033.table
  base := (-6404163873859927206999253399788215907947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-367781225975103353463019882319089968500000000000)
      constant := (3127302458417202098272412784993759391378732036957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/6250000000000000000)
  centralHi := (282362210896690432049/100000000000000000000)
  directionLo := (57348036133565787997/20000000000000000000)
  directionHi := (143370090333914469993/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree034.table
  base := (-6607436169633236052380903301749164043521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-3409226064123750861473914890717588631500000000000)
      constant := (29881694810699061901727421187431605870908923564559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree034.table
  base := (-660755053316006465112570891835539866887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-189450899146675149897782469575762670500000000000)
      constant := (1660984768669143874095535795296581600580712880485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57348036133565787997/20000000000000000000)
  centralHi := (143370090333914469993/50000000000000000000)
  directionLo := (291052305052496153173/100000000000000000000)
  directionHi := (145526152526248076587/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree035.table
  base := (-67744841038463593602630989053018745773/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-877321258743196272288130324363802191312500000000)
      constant := (7922582790834402550260894541252741021638398356675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree035.table
  base := (-6774576916949733905400279264088267015943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-390022370611597246128109995983960713500000000000)
      constant := (3523035738371916424667696313206231726730871425633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291052305052496153173/100000000000000000000)
  centralHi := (145526152526248076587/50000000000000000000)
  directionLo := (7382536714407664147/2500000000000000000)
  directionHi := (295301468576306565881/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree036.table
  base := (-17264357854714133591041424552063082313/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-100259555717272758800864658449800802750000000000)
      constant := (932123863771539131011345008379882158172450910300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree036.table
  base := (-6905818403999276482626878716025331713961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-401142942929844192460655052816396086000000000000)
      constant := (3730492914057461079693267862780266498149252580591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7382536714407664147/2500000000000000000)
  centralHi := (295301468576306565881/100000000000000000000)
  directionLo := (299490351113813799579/100000000000000000000)
  directionHi := (14974517555690689979/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree037.table
  base := (-7001667608898829314734369723864033481029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-3709402976670853544509734110930449032750000000000)
      constant := (35480020708124604603994134285679917592693677094891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree037.table
  base := (-7001728591832627188961843321405884527909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-412263515248091138793200109648831458500000000000)
      constant := (3944334641377324814867630280465567160584073343379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299490351113813799579/100000000000000000000)
  centralHi := (14974517555690689979/5000000000000000000)
  directionLo := (151810723828413688737/50000000000000000000)
  directionHi := (12144857906273095099/4000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree038.table
  base := (-7062615695579093540907905216259455039019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-3809461947519887772188340517668069166500000000000)
      constant := (37460970352018447577250651263055362556040054292101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree038.table
  base := (-1412533014474395790748841353205126887627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-423384087566338085125745166481266831000000000000)
      constant := (4164555856769456343460737790974573575398788355185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151810723828413688737/50000000000000000000)
  centralHi := (12144857906273095099/4000000000000000000)
  directionLo := (307697085693348196509/100000000000000000000)
  directionHi := (30769708569334819651/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree039.table
  base := (-1772217450031044221724018652881539789731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-108597803288025611107415192344602480562500000000)
      constant := (1097202001061141421329195141201206923868668950461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree039.table
  base := (-7088909751945987047678389164746670684017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-434504659884585031458290223313702203500000000000)
      constant := (4391152568392599737296675056433839147270723681127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307697085693348196509/100000000000000000000)
  centralHi := (30769708569334819651/10000000000000000000)
  directionLo := (155859720270450055589/50000000000000000000)
  directionHi := (311719440540900111179/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree040.table
  base := (-283226102632634090113840329806835459209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-4009579889217956227545553331143309434000000000000)
      constant := (41594897392674065805823924332501958369541789577775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree040.table
  base := (-708068487043878070664130692230627614679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-222812616101415988895417640073068788000000000000)
      constant := (2312060814646218592988792038676705775000392396245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155859720270450055589/50000000000000000000)
  centralHi := (311719440540900111179/100000000000000000000)
  directionLo := (315690548921065827023/100000000000000000000)
  directionHi := (19730659307566614189/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree041.table
  base := (-3519069762526314585600179667678008842787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-2054819430033495227612079868940464783875000000000)
      constant := (21873912022660760329110929219716365633835493590973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree041.table
  base := (-35190828149527012160584599960403006187/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-114186451130269731030845084244643237125000000000)
      constant := (1215865139644565035095067307501063093300139219850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315690548921065827023/100000000000000000000)
  centralHi := (19730659307566614189/6250000000000000000)
  directionLo := (319612321015689181781/100000000000000000000)
  directionHi := (159806160507844590891/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree042.table
  base := (-870183633489912011751197812773199233599/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-116936050858778463413965726239404158375000000000)
      constant := (1276612065541682193493118941625228660511572863538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree042.table
  base := (-3480745075143659968246826535332630031371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-233933188419662935227962696905504160500000000000)
      constant := (2554583700224177573794633513519396998228811338301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319612321015689181781/100000000000000000000)
  centralHi := (159806160507844590891/50000000000000000000)
  directionLo := (323486551207292154117/100000000000000000000)
  directionHi := (161743275603646077059/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree043.table
  base := (-428171893838946884219326774006496161099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-1077439200441264727645343137839042458812500000000)
      constant := (12056378607612054756137201783023148558760764008684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree043.table
  base := (-1712691829490847456144609980934914853433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-119746737289393204197117612660860923375000000000)
      constant := (1340310153263298950013436268490802404948215989823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323486551207292154117/100000000000000000000)
  centralHi := (161743275603646077059/50000000000000000000)
  directionLo := (65462985535015173311/20000000000000000000)
  directionHi := (81828731918768966639/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree044.table
  base := (-6706069245730729178988008251965348863781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-4409815772614093138259978958093789969000000000000)
      constant := (50550253295623640578048895049698304051879127549099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree044.table
  base := (-6706082973127808488532280982956327198511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-490107521475819763121015507475879066000000000000)
      constant := (5619678980881125284041513329456226498749787691641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65462985535015173311/20000000000000000000)
  centralHi := (81828731918768966639/25000000000000000000)
  directionLo := (165549520496052964121/50000000000000000000)
  directionHi := (331099040992105928243/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree045.table
  base := (-3263746859646822266918412099569390299517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-250548596859062631441032520268411672375000000000)
      constant := (2940680128452233245083059597165796526581097411627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree045.table
  base := (-1631876196897280142049249250356269856763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-125307023448516677363390141077078609625000000000)
      constant := (1471120386421974517952091869596525590767067627053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165549520496052964121/50000000000000000000)
  centralHi := (331099040992105928243/100000000000000000000)
  directionLo := (16742019592394187781/5000000000000000000)
  directionHi := (334840391847883755621/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree046.table
  base := (-6315077190292352265436979880549934952061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-4609933714312161593617191771569030236500000000000)
      constant := (55371474665931650102970769699204104015852034075219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree046.table
  base := (-789385763770932388134167144739697509341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-128087166528078413946526405285187452750000000000)
      constant := (1538911888011301282221043224688704809611454722742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16742019592394187781/5000000000000000000)
  centralHi := (334840391847883755621/100000000000000000000)
  directionLo := (169270199001327781443/50000000000000000000)
  directionHi := (338540398002655562887/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree047.table
  base := (-606886181312295787677896652904623763113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-2354996342580597910647899089153325185125000000000)
      constant := (28933972492388819565349203824553181285429896675635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree047.table
  base := (-3034434499100679505492853300679147661093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-261734619215280301059325338986592591750000000000)
      constant := (3216588202207012555352547957664568257764843395283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169270199001327781443/50000000000000000000)
  centralHi := (338540398002655562887/100000000000000000000)
  directionLo := (342200400564856924069/100000000000000000000)
  directionHi := (34220040056485692407/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree048.table
  base := (-5788880822370221545844224511325628991153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-534450184001136672108267176116030056000000000000)
      constant := (6713516559245792650463977903176481097453974015143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree048.table
  base := (-2894443303713345768410607410083416041021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-267294905374403774225597867402810278000000000000)
      constant := (3358533816651767380498166828915764508761831707451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342200400564856924069/100000000000000000000)
  centralHi := (34220040056485692407/10000000000000000000)
  directionLo := (43227708708813983399/12500000000000000000)
  directionHi := (345821669670511867193/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree049.table
  base := (-5475160420221263391820510969292437809371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-4910110626859264276653010991781890637750000000000)
      constant := (63032583471988554158803961082907105438674289206709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree049.table
  base := (-2737582538015141283266423832028786339319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-272855191533527247391870395819027964250000000000)
      constant := (3503660434296295635833768729287716244492226615089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/12500000000000000000)
  centralHi := (345821669670511867193/100000000000000000000)
  directionLo := (13976216385311310647/4000000000000000000)
  directionHi := (10918919051024461443/3125000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree050.table
  base := (-5127721264506770524098993967442954007563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-5010169597708298504331617398519510771500000000000)
      constant := (65700745668441536718886983669956655969136875776677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree050.table
  base := (-5127725009937711163797242909353617057061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-556830955385301441116285848470491301000000000000)
      constant := (7303935818497806041754184365296327636085733596691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13976216385311310647/4000000000000000000)
  centralHi := (10918919051024461443/3125000000000000000)
  directionLo := (17647638181043152003/5000000000000000000)
  directionHi := (352952763620863040061/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree051.table
  base := (-4746579641876011879358336669547629038457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-567803174284148081334469311695236767250000000000)
      constant := (7602903727441747411955165263099933671164578880767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree051.table
  base := (-4746582653735299596940442238185298705151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-567951527703548387448830905302926673500000000000)
      constant := (7606912252993091412848314280674204656613330669481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/5000000000000000000)
  centralHi := (352952763620863040061/100000000000000000000)
  directionLo := (356464817919744944719/100000000000000000000)
  directionHi := (4455810223996811809/1250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree052.table
  base := (-21658741963653110605715131354170154707/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-1302571884851591739922207552998687759750000000000)
      constant := (17802186367797702388131009869352630360160480532650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree052.table
  base := (-67683606465043445002579501744226262373/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-144768025005448833445343990533840511500000000000)
      constant := (1979062497684628124929501496803406271483959663408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356464817919744944719/100000000000000000000)
  centralHi := (4455810223996811809/1250000000000000000)
  directionLo := (359942605815856443831/100000000000000000000)
  directionHi := (44992825726982055479/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree053.table
  base := (-1941618820222213398781742567481347429217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3085092)
      previous := (1542546)
      next := (1542546)
      square := (16834243728620751534216792952515000000000000)
      linear := (-945237897873869915871740231173437375000000000)
      constant := (13180594544490677692102134050643057572702603927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree053.table
  base := (-3883239585830475174886611276302411782167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (685576)
      previous := (342788)
      next := (342788)
      square := (3740943050804611452048176211670000000000000)
      linear := (-210107750922051363515101822345246500000000000)
      constant := (2930562082155816646472519368577696385956096153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359942605815856443831/100000000000000000000)
  centralHi := (44992825726982055479/12500000000000000000)
  directionLo := (363387111147961753721/100000000000000000000)
  directionHi := (181693555573980876861/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree054.table
  base := (-1700527683140965987782917521252573396861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-300578082283579745280335723637221739250000000000)
      constant := (4274757587172482873123799702246592640312419170491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree054.table
  base := (-340105692891280392302189856475932006347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-300656622329144613223233037900116395500000000000)
      constant := (4277004417202098968107826518267338813475587036785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363387111147961753721/100000000000000000000)
  centralHi := (181693555573980876861/50000000000000000000)
  directionLo := (36679927155790973009/10000000000000000000)
  directionHi := (366799271557909730091/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree055.table
  base := (-360650982833160887318103306663717347563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-1377616112988367410681162358051902860062500000000)
      constant := (19974978480935788344841081426792477068680830648354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree055.table
  base := (-2885209117417710051113132898660474307817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-612433816976536172779011132632668163500000000000)
      constant := (8882429738777362576094784882013801517524903258927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36679927155790973009/10000000000000000000)
  centralHi := (366799271557909730091/100000000000000000000)
  directionLo := (92544995367917283139/25000000000000000000)
  directionHi := (370179981471669132557/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree056.table
  base := (-1167850045265453305863539145241093080353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-2805261711401251935201627919472615787000000000000)
      constant := (41455705791317365011225765395729222641887238463087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree056.table
  base := (-2335701097731780341708982344391530669329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-623554389294783119111556189465103536000000000000)
      constant := (9217211531853512871404647052227196709553618243399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92544995367917283139/25000000000000000000)
  centralHi := (370179981471669132557/100000000000000000000)
  directionLo := (93382523709376892261/25000000000000000000)
  directionHi := (74706018967501513809/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree057.table
  base := (-70101438442806448390279483650595050871/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-634509154850170899786873582853650189750000000000)
      constant := (9553347671925693826898855716052330618313513570025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree057.table
  base := (-876268384650703508070189505770182289667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-317337480806515032722050623148769454250000000000)
      constant := (4779177079207914450925454071787786183289383326277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93382523709376892261/25000000000000000000)
  centralHi := (74706018967501513809/20000000000000000000)
  directionLo := (47106303455633311461/12500000000000000000)
  directionHi := (376850427645066491689/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree058.table
  base := (-1135718557854299584340987918280694544677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-5810641364500572325760468652420471841500000000000)
      constant := (89106065924857686593138509496339108349133710666283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree058.table
  base := (-567859603111086634222726380610716380853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-322897766965638505888323151564987140500000000000)
      constant := (4952928787467298843626214222390800626523553155843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47106303455633311461/12500000000000000000)
  centralHi := (376850427645066491689/100000000000000000000)
  directionLo := (380141760246387020769/100000000000000000000)
  directionHi := (38014176024638702077/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree059.table
  base := (-485250311958164742402624877636538736837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-5910700335349606553439075059158091975250000000000)
      constant := (92289221905394180817959404955469995197913011490923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree059.table
  base := (-24262541596404173994284829903303185301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-164229026562380989527297839990602413375000000000)
      constant := (2564930436773396041305951195426846493712935120655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380141760246387020769/100000000000000000000)
  centralHi := (38014176024638702077/10000000000000000000)
  directionLo := (383404839497591224521/100000000000000000000)
  directionHi := (191702419748795612261/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree060.table
  base := (198866859971943545554669012219856752909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-667862145133182309013075718432856901000000000000)
      constant := (10614399638297823050530831042474559531151982681621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree060.table
  base := (99433221546397857533573998361313883989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-334018339283885452220868208397422513000000000000)
      constant := (5309973323919977219868828034627390051409330634141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383404839497591224521/100000000000000000000)
  centralHi := (191702419748795612261/50000000000000000000)
  directionLo := (386640380737870917361/100000000000000000000)
  directionHi := (193320190368935458681/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree061.table
  base := (458315723432661021881519892930248395889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3055409138523837504398143936316666121375000000000)
      constant := (49413595125071608872343427932241102490397873057169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree061.table
  base := (916631112730705405687269854658400823777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-679157250886017850774281473627280398500000000000)
      constant := (10986532255846939792068848908615930992528171538313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386640380737870917361/100000000000000000000)
  centralHi := (193320190368935458681/50000000000000000000)
  directionLo := (77969813924127811967/20000000000000000000)
  directionHi := (97462267405159764959/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree062.table
  base := (834021128703509740017933168794453333267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3105438623948354618237447139685476188250000000000)
      constant := (51091001134979811153759593206271421148701941379107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree062.table
  base := (1668041989665304936892919857405964517841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-690277823204264797106826530459715771000000000000)
      constant := (11359478554301883541403855023459609925555632075129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77969813924127811967/20000000000000000000)
  centralHi := (97462267405159764959/25000000000000000000)
  directionLo := (393031563810121969081/100000000000000000000)
  directionHi := (196515781905060984541/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree063.table
  base := (1226549176188669073427466033492100630811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-350607567708096859119638927006031806125000000000)
      constant := (5866335149135224128570452020427103382827759117059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree063.table
  base := (1226549068945998812133781771142333437121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-350699197761255871719685793646075571750000000000)
      constant := (5869392764975401206957248309699967338445859233449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393031563810121969081/100000000000000000000)
  centralHi := (196515781905060984541/50000000000000000000)
  directionLo := (396188494555283714537/100000000000000000000)
  directionHi := (198094247277641857269/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree064.table
  base := (1635899495654100718647415711772537658481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3205497594797388845916053546423096322000000000000)
      constant := (54531640699600037915101306456509766053226597189601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree064.table
  base := (3271798819529326496948000662129014227329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-712518967840758689771916644124586516000000000000)
      constant := (12124453172345170276927122705056200085262383058601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396188494555283714537/100000000000000000000)
  centralHi := (198094247277641857269/50000000000000000000)
  directionLo := (99830117037937933193/25000000000000000000)
  directionHi := (399320468151751732773/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree065.table
  base := (4124143590426967263938009838625996613011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-6511054160443811919510713499583812777750000000000)
      constant := (112589748339860873429513507932209170408151407729731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree065.table
  base := (4124143452884803688186947004321972928133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-723639540159005636104461700957021888500000000000)
      constant := (12516481473248123196218142255686717021919538134477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/25000000000000000000)
  centralHi := (399320468151751732773/100000000000000000000)
  directionLo := (402428067301333079283/100000000000000000000)
  directionHi := (100607016825333269821/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree066.table
  base := (125253292237482146246076969412229274733/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-183642031424801281866369997397817580875000000000)
      constant := (3227039817993429487782816670622510790305604598770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree066.table
  base := (5010131579396287570379495228214287867437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-734760112477252582437006757789457261000000000000)
      constant := (12914870426166343749338734718118551464792557516853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402428067301333079283/100000000000000000000)
  centralHi := (100607016825333269821/25000000000000000000)
  directionLo := (202755926188877622861/50000000000000000000)
  directionHi := (405511852377755245723/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree067.table
  base := (2964881462843990441187918524007963551307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3355586051070940187433963156529526522625000000000)
      constant := (59907168338333659298789507713730947054759094367947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree067.table
  base := (2964881418785183534725996595444158448271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-372940342397749764384775907310946316750000000000)
      constant := (6659810012990512071546772829780388723987170117799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202755926188877622861/50000000000000000000)
  centralHi := (405511852377755245723/100000000000000000000)
  directionLo := (408572362606418178099/100000000000000000000)
  directionHi := (4085723626064181781/1000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree068.table
  base := (688303701294337617259186801965933558699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3405615536495457301273266359898336589500000000000)
      constant := (61756228995058919363314896973563383540215216705895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree068.table
  base := (6883036942436811697433313383041367302813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-757001257113746475102096871454328006000000000000)
      constant := (13730730268656937753803951447361119770498906255397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408572362606418178099/100000000000000000000)
  centralHi := (4085723626064181781/1000000000000000000)
  directionLo := (411610117165191355727/100000000000000000000)
  directionHi := (25725632322824459733/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree069.table
  base := (1967488431438655864154804822141107953427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-191980278995554134172920531292619258687500000000)
      constant := (3535216593315988234516269020498487942473629824163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree069.table
  base := (1967488417337897968440127713872816699451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-192030457357998355358660482071690844625000000000)
      constant := (3537050287753271789442045416475365615243685867219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411610117165191355727/100000000000000000000)
  centralHi := (25725632322824459733/6250000000000000000)
  directionLo := (10365640405315493939/2500000000000000000)
  directionHi := (414625616212619757561/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree070.table
  base := (8890512886339250537084608917368832957817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-7011349014688983057903745533271913446500000000000)
      constant := (131080354761783663081473224545059001859982877319657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree070.table
  base := (4445256420614039158595214222150247430257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-389621200875120183883593492559599375500000000000)
      constant := (7286016335270947878361742339823444761691754833433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10365640405315493939/2500000000000000000)
  centralHi := (414625616212619757561/100000000000000000000)
  directionLo := (417619341849305093167/100000000000000000000)
  directionHi := (26101208865581568323/6250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree071.table
  base := (1988942870908681494866757533497563716551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (3438216)
      previous := (1719108)
      next := (1719108)
      square := (18761115109579722697724646460470000000000000)
      linear := (-1410713744403494799758451089071520250000000000)
      constant := (26770507871351057098388636705294335690028129155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree071.table
  base := (994471431847083312816553257356027446457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (191012)
      previous := (95506)
      next := (95506)
      square := (1042284172754429038762480358915000000000000)
      linear := (-78393470945098920263809962502641750000000000)
      constant := (1488020712682668970281999681406403327360488565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417619341849305093167/100000000000000000000)
  centralHi := (26101208865581568323/6250000000000000000)
  directionLo := (8411835180353900509/2000000000000000000)
  directionHi := (420591759017695025451/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree072.table
  base := (11032558019879230785519058291452111294209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-801274106265227945917884260749683746000000000000)
      constant := (15430791510931764702533655116485533430832808161321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree072.table
  base := (1103255799103997817885869839001450511539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-400741773193367130216138549392034748000000000000)
      constant := (7719388806814611145858827150036331173442643450455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8411835180353900509/2000000000000000000)
  centralHi := (420591759017695025451/100000000000000000000)
  directionLo := (52942914543129456009/12500000000000000000)
  directionHi := (423543316345035648073/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree073.table
  base := (3038510948811778505014144537237924992703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-1827881481809021435234891188371193461937500000000)
      constant := (35715333751849791806596685887974100530834843596263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree073.table
  base := (2430808754439039043565682773435430965203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-812604118704981206764822155616504868500000000000)
      constant := (15881691034401299391172888912136226835619287996535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52942914543129456009/12500000000000000000)
  centralHi := (423543316345035648073/100000000000000000000)
  directionLo := (85294889386762918193/20000000000000000000)
  directionHi := (213237223466907295483/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree074.table
  base := (13309171611986360201371064234635693641581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-7411584898085119968618171160222393981500000000000)
      constant := (146902764397770309888113804704761181266916861484701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree074.table
  base := (266183431871277125861974482778091525049/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-411862345511614076548683606224470120500000000000)
      constant := (8165482543307365944987360609644542693991539332025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85294889386762918193/20000000000000000000)
  centralHi := (213237223466907295483/50000000000000000000)
  directionLo := (429385569103638057947/100000000000000000000)
  directionHi := (107346392275909514487/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree075.table
  base := (7248970707986565779499049996263562526033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-417313548274119677572043198164445228625000000000)
      constant := (8388967320144538116675491410260713997797412929577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree075.table
  base := (115983531210024209801488587820366380169/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-834845263341475099429912269281375613500000000000)
      constant := (16786599769506386718075618739706782269232661070125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429385569103638057947/100000000000000000000)
  centralHi := (107346392275909514487/25000000000000000000)
  directionLo := (43227708708813983399/10000000000000000000)
  directionHi := (432277087088139833991/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree076.table
  base := (7860176582272044490288056468038215312377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3805851419891594211987691986848817124500000000000)
      constant := (77578638548228107517551858446026892889722315005417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree076.table
  base := (7860176576392198269315536799598358196337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-422982917829861022881228663056905493000000000000)
      constant := (8624297541237381924314472091326307705932667100953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43227708708813983399/10000000000000000000)
  centralHi := (432277087088139833991/100000000000000000000)
  directionLo := (217574695845104725947/50000000000000000000)
  directionHi := (87029878338041890379/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree077.table
  base := (8488203412035502704755520689492867826403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3855880905316111325826995190217627191375000000000)
      constant := (79685180197524132144161359462987178356241731028963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree077.table
  base := (16976406814677973157871765852722499843333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-857086407977968992095002382946246358500000000000)
      constant := (17716951025045780907405741443655503538477818803277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217574695845104725947/50000000000000000000)
  centralHi := (87029878338041890379/20000000000000000000)
  directionLo := (219001430449273220717/50000000000000000000)
  directionHi := (87600572179709288287/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree078.table
  base := (1826610236804860700304927245217127095981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-433990043415625382185144265954048584250000000000)
      constant := (9091147869722220080376323124120741963289725903945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree078.table
  base := (18266102360547205549009971355833993641017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-868206980296215938427547439778681731000000000000)
      constant := (18191667596845799879518972080950001118276726051873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219001430449273220717/50000000000000000000)
  centralHi := (87600572179709288287/20000000000000000000)
  directionLo := (110209465117073633199/25000000000000000000)
  directionHi := (440837860468294532797/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree079.table
  base := (9794719887793521382020824771448166557299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-3955939876165145553505601596955247325125000000000)
      constant := (83984090436824536062958476817028204100922736961779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree079.table
  base := (19589439769597307684589417029164996405073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-879327552614462884760092496611117103500000000000)
      constant := (18672744797580363080501016627622132326823976137337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110209465117073633199/25000000000000000000)
  centralHi := (440837860468294532797/100000000000000000000)
  directionLo := (22182737223414044671/5000000000000000000)
  directionHi := (443654744468280893421/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree080.table
  base := (20946419030223362831797771265117034640617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-8011938723179325334689809600648114784000000000000)
      constant := (172352918048897532955359008262885574107609918858457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree080.table
  base := (5236604756360358171440512699168310409309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-222612031233177457773159388360888119000000000000)
      constant := (4790045656754357497292566035238584454840274613221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22182737223414044671/5000000000000000000)
  centralHi := (443654744468280893421/100000000000000000000)
  directionLo := (446453855797178340827/100000000000000000000)
  directionHi := (111613463949294585207/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree081.table
  base := (22337040118984502677043684203387374140421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-901333077114262173596490667487303879750000000000)
      constant := (19643874797676892984384239830190363305005528591149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree081.table
  base := (698032503598982036876601050261634488633/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-225392174312739194356295652568996962125000000000)
      constant := (4913495271243540575824546865861702590063112371816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446453855797178340827/100000000000000000000)
  centralHi := (111613463949294585207/25000000000000000000)
  directionLo := (449235526670720699369/100000000000000000000)
  directionHi := (44923552667072069937/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree082.table
  base := (1485081439478034623067319688836320021093/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-2053014166219348447511755603530838762875000000000)
      constant := (45323511565732472073256783887100083912021813509812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree082.table
  base := (2376130302860211467180755038554764820499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-456344634784601861878863833554211610500000000000)
      constant := (10077070085653253104700288556416901921255102521655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449235526670720699369/100000000000000000000)
  centralHi := (44923552667072069937/10000000000000000000)
  directionLo := (226000039540965515079/50000000000000000000)
  directionHi := (452000079081931030159/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree083.table
  base := (25219207760162364037919559668002935530821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-8312115635726428017725628820860975185250000000000)
      constant := (185850437299384781230958667899370520264098708118741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree083.table
  base := (6304801939432834672704346851590090780593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-230952460471862667522568180985214648375000000000)
      constant := (5165164971475244953126437713178340069576976300217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226000039540965515079/50000000000000000000)
  centralHi := (452000079081931030159/100000000000000000000)
  directionLo := (113686956309041892219/25000000000000000000)
  directionHi := (454747825236167568877/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree084.table
  base := (26710754298182384167403376865287209637327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-934686067397273582822692803066510591000000000000)
      constant := (21162671809738698241814083781019722495377979028263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree084.table
  base := (1335537714812136702048892647423410883283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-233732603551424404105704445193323491500000000000)
      constant := (5293385057167049745741877898727103151193632774135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113686956309041892219/25000000000000000000)
  centralHi := (454747825236167568877/100000000000000000000)
  directionLo := (228739533981325634129/50000000000000000000)
  directionHi := (457479067962651268259/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree085.table
  base := (28235942640712686631076729838512393558371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-8512233577424496473082841634336215452750000000000)
      constant := (195134873227083708500866299926007033662390340022291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree085.table
  base := (28235942639165310985107726632004576425587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-946050986523944562755362837605729338500000000000)
      constant := (21692781199537773666010107675213805067053477844203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228739533981325634129/50000000000000000000)
  centralHi := (457479067962651268259/100000000000000000000)
  directionLo := (230097050552005226279/50000000000000000000)
  directionHi := (460194101104010452559/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree086.table
  base := (14897386391909794468704531561403664064801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-4306146274136765350380724020536917793250000000000)
      constant := (99931459058594869862362790991720535641563157002321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree086.table
  base := (14897386391292662554752270713449638898481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-478585779421095754543953947219082355500000000000)
      constant := (11109191399227142289656353122383408047478964803289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230097050552005226279/50000000000000000000)
  centralHi := (460194101104010452559/100000000000000000000)
  directionLo := (18515728395410439951/4000000000000000000)
  directionHi := (57861651235657624847/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree087.table
  base := (31387244724406674586406627290051546497067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-968039057680284992048894938645717302250000000000)
      constant := (22738686773063529535499544475985229205945764224323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree087.table
  base := (31387244723422297441599487521109943777833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-968292131160438455420452951270600083500000000000)
      constant := (22750345025374111620022786592500067380818363733777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18515728395410439951/4000000000000000000)
  centralHi := (57861651235657624847/12500000000000000000)
  directionLo := (232788335631766775193/50000000000000000000)
  directionHi := (465576671263533550387/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree088.table
  base := (33013358460037429843514606516394925351669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-8812410489971599156118660854549075854000000000000)
      constant := (209490661747919273768908198840818680582998157248549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree088.table
  base := (33013358459252451527102158553116215167897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-979412703478685401752998008103035456000000000000)
      constant := (23288667880262933703929375789255755541417784894593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232788335631766775193/50000000000000000000)
  centralHi := (465576671263533550387/100000000000000000000)
  directionLo := (468244754259761551517/100000000000000000000)
  directionHi := (234122377129880775759/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree089.table
  base := (17336556994397710206300847930023983512649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-4456234730410316691898633630643347993875000000000)
      constant := (107195180243994015135683469868399727213467630049129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree089.table
  base := (17336556994084765421556607882139404284083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-495266637898466174042771532467735414250000000000)
      constant := (11916675681546878958255433414111649056893814290027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468244754259761551517/100000000000000000000)
  centralHi := (234122377129880775759/50000000000000000000)
  directionLo := (5886221503418180969/1250000000000000000)
  directionHi := (470897720273454477521/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree090.table
  base := (36366511309174064021790985927568458984653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1001392047963296401275097074224924013500000000000)
      constant := (24371919686398448243403610457103324599386004886357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree090.table
  base := (7273302261735016850871882218352256267529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1001653848115179294418088121767906201000000000000)
      constant := (24384395473845365936453548655654008450772599262005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5886221503418180969/1250000000000000000)
  centralHi := (470897720273454477521/100000000000000000000)
  directionLo := (94707164676319748107/20000000000000000000)
  directionHi := (59191977922699842567/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree091.table
  base := (38093550419989735909782258421663638673529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-9112587402518701839154480074761936255250000000000)
      constant := (224361411816562442586831500214771061643159895697609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree091.table
  base := (2380846901224498870338534294210692818571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-253193605108356560187658294650085393375000000000)
      constant := (6235450053125272351588218117982896275695644293996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94707164676319748107/20000000000000000000)
  centralHi := (59191977922699842567/12500000000000000000)
  directionLo := (119039827655663414539/25000000000000000000)
  directionHi := (476159310622653658157/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree092.table
  base := (19927115660156634740224382380728519179361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-4606323186683868033416543240749778194500000000000)
      constant := (114716382202399420527845586245695693305982937648081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree092.table
  base := (39854231319996244347363670355040934850013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1023894992751673187083178235432776946000000000000)
      constant := (25505565579047844620209980500508170038894173732197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119039827655663414539/25000000000000000000)
  centralHi := (476159310622653658157/100000000000000000000)
  directionLo := (239384211133270477681/50000000000000000000)
  directionHi := (478768422266540955363/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree093.table
  base := (41648554009415959244165804875009638930539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1034745038246307810501299209804130724750000000000)
      constant := (26062370549133595806805854383050464254033849001091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree093.table
  base := (41648554009163307945631131930879171754801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1035015565069920133415723292265212318500000000000)
      constant := (26075691573475371635357722478602803812221758721369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239384211133270477681/50000000000000000000)
  centralHi := (478768422266540955363/100000000000000000000)
  directionLo := (96272678414292591171/20000000000000000000)
  directionHi := (30085212004466434741/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree094.table
  base := (5434564810840874615505471485824566492827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-2353191078766451130547574823743699164125000000000)
      constant := (59936780857175065382127462608406249089046454439734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree094.table
  base := (43476518486525671250893711824116341931927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1046136137388167079748268349097647691000000000000)
      constant := (26652178195775634535082704952244538735792872815663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96272678414292591171/20000000000000000000)
  centralHi := (30085212004466434741/6250000000000000000)
  directionLo := (483944447528326397757/100000000000000000000)
  directionHi := (241972223764163198879/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree095.table
  base := (45338124751799921056584289344748203123107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-9512823285914838749868905701712416790250000000000)
      constant := (244990129864235641129486536373897983237674143825747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree095.table
  base := (45338124751639512462706050867402320850389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1057256709706414026080813405930083063500000000000)
      constant := (27235025445942348727684737360357997764077481955741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483944447528326397757/100000000000000000000)
  centralHi := (241972223764163198879/50000000000000000000)
  directionLo := (121627952523373805271/25000000000000000000)
  directionHi := (97302362018699044217/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree096.table
  base := (2361668640214308622136680872574131518371/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-267024507132329804931875336345834359000000000000)
      constant := (6952509840243446670824911025213335480641799823495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree096.table
  base := (9446674560831675834722920692872697688289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1068377282024660972413358462762518436000000000000)
      constant := (27824233323970608388523820637649324649760407804205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121627952523373805271/25000000000000000000)
  centralHi := (97302362018699044217/20000000000000000000)
  directionLo := (489065695410546306787/100000000000000000000)
  directionHi := (122266423852636576697/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree097.table
  base := (4916226264391425148587200785111666477699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-4856470613806453602613059257593828528875000000000)
      constant := (127823898291125489133798262422942884531387584450895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree097.table
  base := (49162262643812453027297276071324610588209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1079497854342907918745903519594953808500000000000)
      constant := (28419801829856592844075131721106269196631978847321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489065695410546306787/100000000000000000000)
  centralHi := (122266423852636576697/25000000000000000000)
  directionLo := (245803156760828313457/50000000000000000000)
  directionHi := (98321262704331325383/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree098.table
  base := (25562397135236645856941292655708351265537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-4906500099230970716452362460962638595750000000000)
      constant := (130531228432334731169625620759575989909229185161777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree098.table
  base := (1278119856759805225056357543468993988043/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-272654606665288716269612144106847295250000000000)
      constant := (7255432740899333796156126319315732449400478592670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245803156760828313457/50000000000000000000)
  centralHi := (98321262704331325383/20000000000000000000)
  directionLo := (123533467267302064021/25000000000000000000)
  directionHi := (98826773813841651217/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree099.table
  base := (664012096047501433724110248476936499067/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-275362754703082657238425870240636036812500000000)
      constant := (7403731530444409351597100813604162648243250621460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree099.table
  base := (5312096768373553885197798594234792940683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-550869499489700905705496816629912276750000000000)
      constant := (14815010362595269965002549345927273199897266277135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123533467267302064021/25000000000000000000)
  centralHi := (98826773813841651217/20000000000000000000)
  directionLo := (496648561488158892363/100000000000000000000)
  directionHi := (124162140372039723091/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree100.table
  base := (11030156576753805880233183817211714888819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-10013118140160009888261937735400517459000000000000)
      constant := (272063431276222782965418120764975697631622196268495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree100.table
  base := (689384786046470064886339792906427941349/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-278214892824412189435884672523064981500000000000)
      constant := (7561167778658609840434961997078397863591478559620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496648561488158892363/100000000000000000000)
  centralHi := (124162140372039723091/25000000000000000000)
  directionLo := (99830117037937933193/20000000000000000000)
  directionHi := (249575292594844832983/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree101.table
  base := (7151779983785474368902349395278481484989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-2528294277752261028985136035534534398187500000000)
      constant := (69412436351332334044965216969135662949962408031538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree101.table
  base := (57214239870242847985399803960788210203419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1123980143615895704076083746924695298500000000000)
      constant := (30865682131927680333602735483208471156781687417811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99830117037937933193/20000000000000000000)
  centralHi := (249575292594844832983/50000000000000000000)
  directionLo := (250820064868304414183/50000000000000000000)
  directionHi := (501640129736608828367/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree102.table
  base := (59311338643271288788486151332944415992253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1134804009095342038179905616541750858500000000000)
      constant := (31477030831478786383400985356670628916150355170757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree102.table
  base := (1853479332601208987939151197408431259489/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-283775178983535662602157200939282667750000000000)
      constant := (7873263444267308776472184637253903059617726749128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250820064868304414183/50000000000000000000)
  centralHi := (501640129736608828367/100000000000000000000)
  directionLo := (504117380010959187041/100000000000000000000)
  directionHi := (252058690005479593521/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree103.table
  base := (61442079202676519081524056737160193252249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-10313295052707112571297756955613377860250000000000)
      constant := (288994027510154998535020331590303916823493986730729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree103.table
  base := (61442079202650565158026221910079891925697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1146221288252389596741173860589566043500000000000)
      constant := (32126786050058331115086624587151586523513354962793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504117380010959187041/100000000000000000000)
  centralHi := (252058690005479593521/50000000000000000000)
  directionLo := (253291258187124338881/50000000000000000000)
  directionHi := (506582516374248677763/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree104.table
  base := (15901615387114674181649945890273427586499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-2603338505889036699744090840587749498500000000000)
      constant := (73687998871465475301918833101820026453381791624979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree104.table
  base := (63606461548438036653363883333422199128633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1157341860570636543073718917422001416000000000000)
      constant := (32766878950894395667831745717925754922013096018977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253291258187124338881/50000000000000000000)
  centralHi := (506582516374248677763/100000000000000000000)
  directionLo := (254517857410348530797/50000000000000000000)
  directionHi := (101807142964139412319/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree105.table
  base := (8225560710073517812708283810475769367827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-292039249844588361851526938030239392437500000000)
      constant := (8349088372511833419538169345351208772890891340526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree105.table
  base := (65804485680571698006763856545951257961819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1168462432888883489406263974254436788500000000000)
      constant := (33413332479577012397193654334163236710845702587411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254517857410348530797/50000000000000000000)
  centralHi := (101807142964139412319/20000000000000000000)
  directionLo := (511477147123867228731/100000000000000000000)
  directionHi := (127869286780966807183/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree106.table
  base := (13607230319808770489536340997174477115837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6170184)
      previous := (3085092)
      next := (3085092)
      square := (33668487457241503068433585905030000000000000)
      linear := (-3778380906106876203037940966830273500000000000)
      constant := (109092055992824716071779748442976776355092044265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree106.table
  base := (68036151599030764551932260146083646888751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (685576)
      previous := (342788)
      next := (342788)
      square := (3740943050804611452048176211670000000000000)
      linear := (-419929870134257898091423649372329000000000000)
      constant := (12127499692454925948303674073176096038966193791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511477147123867228731/100000000000000000000)
  centralHi := (127869286780966807183/25000000000000000000)
  directionLo := (513906980977026832737/100000000000000000000)
  directionHi := (256953490488513416369/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree107.table
  base := (70301459303811582000443854979561686899971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-10713530936103249482012182582563858395250000000000)
      constant := (312369207106115958885513068629459444882319016595891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree107.table
  base := (14060291860760233298464576818109890979351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1190703577525377382071354087919307533500000000000)
      constant := (34725321420480820211908954179568806857289678351595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513906980977026832737/100000000000000000000)
  centralHi := (256953490488513416369/50000000000000000000)
  directionLo := (516325380127564826781/100000000000000000000)
  directionHi := (258162690063782413391/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree108.table
  base := (72600408794882338921071726026521750909289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1201509989661364856632309887700164281000000000000)
      constant := (35372894097470983493158352546982266362426435909841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree108.table
  base := (14520081758974810171161330470564213265383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1201824149843624328403899144751742906000000000000)
      constant := (35390856832701686706983955451865216441449325648635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516325380127564826781/100000000000000000000)
  centralHi := (258162690063782413391/50000000000000000000)
  directionLo := (129683126126441950197/25000000000000000000)
  directionHi := (518732504505767800789/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree109.table
  base := (74933000072251198349988823459442699528889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-10913648877801317937369395396039098662750000000000)
      constant := (324400104597212677472770486360214262079393535100169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree109.table
  base := (37466500036122301873708936573305704837427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-606472361080935637368222100792089139250000000000)
      constant := (18031376436384209154221880921772572855458958845163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129683126126441950197/25000000000000000000)
  centralHi := (518732504505767800789/100000000000000000000)
  directionLo := (104225702069648541783/20000000000000000000)
  directionHi := (130282127587060677229/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree110.table
  base := (38649616567958185829959907945608846299351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-5506853924325176082524000901388359398250000000000)
      constant := (165250690133018604521584269311914551917741387752871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree110.table
  base := (19324808283977781236037642802654299015847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-306016323620029555267247314604153412750000000000)
      constant := (9185252385170247735210817764224680233734677198143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104225702069648541783/20000000000000000000)
  centralHi := (130282127587060677229/25000000000000000000)
  directionLo := (52351355031625552429/10000000000000000000)
  directionHi := (523513550316255524291/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree111.table
  base := (9962388498234809406300976063104666938009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-308715744986094066464628005819842748062500000000)
      constant := (9351663163436459019569851298424117461364574302042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree111.table
  base := (15939821597174860253714838872306777052897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1235185866798365167401534315249049023500000000000)
      constant := (37425626836439414329706139487247030845415467297965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52351355031625552429/10000000000000000000)
  centralHi := (523513550316255524291/100000000000000000000)
  directionLo := (262943886804619732807/50000000000000000000)
  directionHi := (105177554721847893123/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree112.table
  base := (82132624622139956831520070797030325514891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-11213825790348420620405214616251959064000000000000)
      constant := (342875585450238936396702750555511646104742817189211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree112.table
  base := (20533156155534159130975627254614365068431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-311576609779153028433519843020371099000000000000)
      constant := (9529151190010930982327254202552749847196679524839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262943886804619732807/50000000000000000000)
  centralHi := (105177554721847893123/20000000000000000000)
  directionLo := (528251326073711619383/100000000000000000000)
  directionHi := (66031415759213952423/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree113.table
  base := (42299891522352322867831026090294530848131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-5656942380598727424041910511494789598875000000000)
      constant := (174574257482808466067839507561207088258216453397251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree113.table
  base := (21149945761175501179255971103465946355341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-314356752858714765016656107228479942125000000000)
      constant := (9703485827873493649061037374564221273097500112629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528251326073711619383/100000000000000000000)
  centralHi := (66031415759213952423/12500000000000000000)
  directionLo := (106120870061564590203/20000000000000000000)
  directionHi := (66325543788477868877/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree114.table
  base := (43550291626788700442292638349914467073277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-634107985113693837542357079429288851750000000000)
      constant := (19748814579435951730545659702902858031224412703813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree114.table
  base := (17420116650715060069263781017024169973217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1268547583753106006399169485746355141000000000000)
      constant := (39517642490790235637435776854752605497902390968365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106120870061564590203/20000000000000000000)
  centralHi := (66325543788477868877/12500000000000000000)
  directionLo := (532946985761753783631/100000000000000000000)
  directionHi := (33309186610109611477/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree115.table
  base := (44817512624381917813242064785709537328241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-5757001351447761651720516918232409732625000000000)
      constant := (180933013921465124406381562100347839475360278044561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree115.table
  base := (89635025248762165088670656170088309392651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1279668156071352952731714542578790513500000000000)
      constant := (40227702297932586939982006758491641629517975518019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532946985761753783631/100000000000000000000)
  centralHi := (33309186610109611477/6250000000000000000)
  directionLo := (53527936883415475663/10000000000000000000)
  directionHi := (535279368834154756631/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree116.table
  base := (46101554515135051531519729220318363121553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-5807030836872278765559820121601219799500000000000)
      constant := (184155305602433534642569919324115139999628522202113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree116.table
  base := (92203109030268774600894630989626774632861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1290788728389599899064259599411225886000000000000)
      constant := (40944122732921115952227032596715750959226224713509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53527936883415475663/10000000000000000000)
  centralHi := (535279368834154756631/100000000000000000000)
  directionLo := (537601632964821994863/100000000000000000000)
  directionHi := (33600102060301374679/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree117.table
  base := (11850604324762841119838217010884190296071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-325392240127599771077729073609446103687500000000)
      constant := (10411455903212734006119438437253875089859410166998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree117.table
  base := (9480483459810167260397824894849735831649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-650954650353923422698402328121830629250000000000)
      constant := (20833451897877957667182962537535115123954401943405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537601632964821994863/100000000000000000000)
  centralHi := (33600102060301374679/6250000000000000000)
  directionLo := (539913908723784665747/100000000000000000000)
  directionHi := (134978477180946166437/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree118.table
  base := (121800252440335602577256568226228524009/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-2953544903860656496619213264169419966625000000000)
      constant := (95342857943826294059456104644765668805994333037800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree118.table
  base := (97440201952267642140398270228249236446497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1313029873026093791729349713076096631000000000000)
      constant := (42396045486437081135426489296298286509578356977993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539913908723784665747/100000000000000000000)
  centralHi := (134978477180946166437/25000000000000000000)
  directionLo := (271108161948486611677/50000000000000000000)
  directionHi := (108443264779394644671/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree119.table
  base := (100109211092774273824677659452951998740831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-11914238586291660214155459463415300000250000000000)
      constant := (387987668983808206143712226597018703949545024943951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree119.table
  base := (3128412846649175188755815983482674238467/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-331037611336085184515473692477133000875000000000)
      constant := (10782886951241177845962982098842006694145049667384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271108161948486611677/50000000000000000000)
  centralHi := (108443264779394644671/20000000000000000000)
  directionLo := (544509003568627386753/100000000000000000000)
  directionHi := (272254501784313693377/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree120.table
  base := (102811862019627081210901445399951879968927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1334921950793410493537118430016991126000000000000)
      constant := (43851236015685378121423734751342220519727721068663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree120.table
  base := (102811862019626550322376415692079150265153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1335271017662587684394439826740967376000000000000)
      constant := (43873410751338905002852410134212258099130961290857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544509003568627386753/100000000000000000000)
  centralHi := (272254501784313693377/50000000000000000000)
  directionLo := (273396035100297115029/50000000000000000000)
  directionHi := (546792070200594230059/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree121.table
  base := (10554815473283388761816334618977835710369/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-6057178263994864334756336138445270133875000000000)
      constant := (200695898623693328529975761153568243491974422906245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree121.table
  base := (13193519341604183198901388588093329929099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-336597897495208657681746220893350687125000000000)
      constant := (11155408581389940245141353074812783029973537215462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273396035100297115029/50000000000000000000)
  centralHi := (546792070200594230059/100000000000000000000)
  directionLo := (274532821854329316281/50000000000000000000)
  directionHi := (549065643708658632563/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree122.table
  base := (108318089232401638001944351102361472952491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-12214415498838762897191278683628160401500000000000)
      constant := (408179688302463853120815729792607190297709563778811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree122.table
  base := (108318089232401302536822840859468946290247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1357512162299081577059529940405838121000000000000)
      constant := (45376218527627377739937879851858853981096820571743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274532821854329316281/50000000000000000000)
  centralHi := (549065643708658632563/100000000000000000000)
  directionLo := (551329841536040711181/100000000000000000000)
  directionHi := (275664920768020355591/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree123.table
  base := (111121665518337205117925341690510218773307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1368274941076421902763320565596197837250000000000)
      constant := (46113866367377874127760407572689212698580437308883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree123.table
  base := (22224333103667387695575436804720593740443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1368632734617328523392074997238273493500000000000)
      constant := (46137163357541852664964384144158842939818825074335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551329841536040711181/100000000000000000000)
  centralHi := (275664920768020355591/50000000000000000000)
  directionLo := (276792389362093849561/50000000000000000000)
  directionHi := (553584778724187699123/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree124.table
  base := (113958883590647364457278700336838928508077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-12414533440536831352548491497103400669000000000000)
      constant := (421927124259198562625935867875957633626454593665117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree124.table
  base := (14244860448830894066993135934055980385031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-344938326733893867431155013517677216500000000000)
      constant := (11726117203825820437288010340844940573300448060478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276792389362093849561/50000000000000000000)
  centralHi := (553584778724187699123/100000000000000000000)
  directionLo := (555830567980981012029/100000000000000000000)
  directionHi := (55583056798098101203/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree125.table
  base := (11682974344933877596616371914200534891739/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-6257296205692932790113548951920510401375000000000)
      constant := (214443334580428894151380323625731228331501911225095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree125.table
  base := (58414871724669303772680719574948100737771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-695436939626911208028582555451572119250000000000)
      constant := (23839067450455879669680526262701597114472737043299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555830567980981012029/100000000000000000000)
  centralHi := (55583056798098101203/10000000000000000000)
  directionLo := (279033659873236463017/50000000000000000000)
  directionHi := (111613463949294585207/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree126.table
  base := (14966780636802246381029475537316486192923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-350406982839858327997380675293851137125000000000)
      constant := (12108428666982760459787058783493479391541850067974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree126.table
  base := (23946849018883567441458444340783952353381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1401994451572069362389710167735579611000000000000)
      constant := (48458161614367377953904123441575485779434113406945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279033659873236463017/50000000000000000000)
  centralHi := (111613463949294585207/20000000000000000000)
  directionLo := (560295142256261353567/100000000000000000000)
  directionHi := (17509223195508167299/3125000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree127.table
  base := (95837803535852612242212142199717326439/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-3178677588270983508896077679329065267562500000000)
      constant := (110744353202691035557869230096879152867497804965080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree127.table
  base := (30668097131472809328942797351537262183759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-353278755972579077180563806142003745875000000000)
      constant := (12311137238917557039576415316021849270280273995271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560295142256261353567/100000000000000000000)
  centralHi := (17509223195508167299/3125000000000000000)
  directionLo := (112502828320521123411/20000000000000000000)
  directionHi := (17578566925081425533/3125000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree128.table
  base := (125644173743765144642008593527529609453227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-12814769323932968263262917124053881204000000000000)
      constant := (450108611559012881952981266850506389633255227238267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree128.table
  base := (7852760858985316258423662344932746592961/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-356058899052140813763700070350112589000000000000)
      constant := (12509324231205099621420064755029200053562007881636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112502828320521123411/20000000000000000000)
  centralHi := (17578566925081425533/3125000000000000000)
  directionLo := (17647638181043152003/3125000000000000000)
  directionHi := (564724421793380864097/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree129.table
  base := (128649600748045478347231703614552318202791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1434980921642444721215724836754611259750000000000)
      constant := (50810780917347374852078854812335412754054234331679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree129.table
  base := (128649600748045411203367226509159959216531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1435356168526810201387345338232885728500000000000)
      constant := (50836405521817975391492740180995117669382936553739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17647638181043152003/3125000000000000000)
  centralHi := (564724421793380864097/100000000000000000000)
  directionLo := (7086576060112047733/1250000000000000000)
  directionHi := (566926084808963818641/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree130.table
  base := (13168866953873830134657996753254595839337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-6507443632815518359310064968764560735750000000000)
      constant := (232271331451052688245920280382780838303073769557885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree130.table
  base := (6584433476936912400085246650332851750941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-361619185211264286929972598766330275250000000000)
      constant := (12910468686665760808667273936242021776320102345145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7086576060112047733/1250000000000000000)
  centralHi := (566926084808963818641/100000000000000000000)
  directionLo := (56911923065713790081/10000000000000000000)
  directionHi := (569119230657137900811/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree131.table
  base := (134761380115849422412873974565220979327531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-13114946236480070946298736344266741605250000000000)
      constant := (471845515496950630701217268572567635274946045314651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree131.table
  base := (33690345028962345008403417828367154574689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-364399328290826023513108862974439118375000000000)
      constant := (13113426149838921069691312682715765588975156862441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56911923065713790081/10000000000000000000)
  centralHi := (569119230657137900811/100000000000000000000)
  directionLo := (142825989356525338639/25000000000000000000)
  directionHi := (571303957426101354557/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree132.table
  base := (137867732479384503643554149545613531102471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1468333911925456130441926972333817971000000000000)
      constant := (53245065115629206431461074964404987645472745677599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree132.table
  base := (137867732479384469977769996497113524647879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1468717885481551040384980508730191846000000000000)
      constant := (53271895079895978708268257854773916260699632131551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142825989356525338639/25000000000000000000)
  centralHi := (571303957426101354557/100000000000000000000)
  directionLo := (57348036133565787997/10000000000000000000)
  directionHi := (573480361335657879971/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree133.table
  base := (141007726629349062378056488387271535069701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-13315064178178139401655949157741981872750000000000)
      constant := (486622874533242761175767375688165768812498473955221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree133.table
  base := (70503863314674517817865467331079596089507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-739919228899898993358762782781313609250000000000)
      constant := (27048223094142002328090336534739367707626033246683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57348036133565787997/10000000000000000000)
  centralHi := (573480361335657879971/100000000000000000000)
  directionLo := (575648536786665359689/100000000000000000000)
  directionHi := (57564853678666535969/10000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree134.table
  base := (144181362565748473706221947302845070534147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-13415123149027173629334555564479602006500000000000)
      constant := (494097380974691025588695214705964800832067726117587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree134.table
  base := (1802267032071855655809101186222964264529/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-372739757529511233262517655598765647750000000000)
      constant := (13731839481129959559971337057955743556677576908020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575648536786665359689/100000000000000000000)
  centralHi := (57564853678666535969/10000000000000000000)
  directionLo := (577808576408814581277/100000000000000000000)
  directionHi := (288904288204407290639/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree135.table
  base := (147388640288587973401403815460628683307983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1501686902208467539668129107913024682250000000000)
      constant := (55736567262778702041872549575000251862474455829127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree135.table
  base := (147388640288587956530173517602486306544061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1502079602436291879382615679227497963500000000000)
      constant := (55764630288603553602953412888481939333193459706309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577808576408814581277/100000000000000000000)
  centralHi := (288904288204407290639/50000000000000000000)
  directionLo := (289980285553403188021/50000000000000000000)
  directionHi := (579960571106806376043/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree136.table
  base := (75314779898936330574566485782015463717201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-6807620545362621042345884188977421137000000000000)
      constant := (254609023852097644725960623484853530307390409302721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree136.table
  base := (75314779898936323874877757715935336293657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-756600087377269412857580368029966668000000000000)
      constant := (28304131640267611480540609817993043787990016748033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289980285553403188021/50000000000000000000)
  centralHi := (579960571106806376043/100000000000000000000)
  directionLo := (291052305052496153173/50000000000000000000)
  directionHi := (582104610104992306347/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree137.table
  base := (153904121093607503971415386320161832509843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-13715300061574276312370374784692462407750000000000)
      constant := (516864207992252571818739398468074730075725076891203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree137.table
  base := (30780824218721498666001903062822629212859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1524320747072785772047705792892368708500000000000)
      constant := (57458256900314916650752768024124790167735852065855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291052305052496153173/50000000000000000000)
  centralHi := (582104610104992306347/100000000000000000000)
  directionLo := (18257524405954403939/3125000000000000000)
  directionHi := (584240780990540926049/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree138.table
  base := (157212324175797339769665233544732885285909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1535039892491478948894331243492231393500000000000)
      constant := (58285287358797864669646896781348657857099834758621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree138.table
  base := (39303081043949332829753126803841134797273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-383860329847758179595062712431201020250000000000)
      constant := (14578652786985675794886614588957511722224916419137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18257524405954403939/3125000000000000000)
  centralHi := (584240780990540926049/100000000000000000000)
  directionLo := (117273833951037740241/20000000000000000000)
  directionHi := (293184584877594350603/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree139.table
  base := (160554169044446880927256895432031720379273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-13915418003272344767727587598167702675250000000000)
      constant := (532328182414980520629474031041171966196342185494233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree139.table
  base := (160554169044446874216697926711453683161073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1546561891709279664712795906557239453500000000000)
      constant := (59177326023418649277257760567606206304326997901337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117273833951037740241/20000000000000000000)
  centralHi := (293184584877594350603/50000000000000000000)
  directionLo := (147122465208907974983/25000000000000000000)
  directionHi := (588489860835631899933/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree140.table
  base := (1311437245596485743414105319202476615597/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-14015476974121378995406194004905322809000000000000)
      constant := (540145996549652372644776479217896833101701750379625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree140.table
  base := (81964827849780356299133479858113303034539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-778841232013763305522670481694837413000000000000)
      constant := (30023200763371409973603665330496873805867285077091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147122465208907974983/25000000000000000000)
  centralHi := (588489860835631899933/100000000000000000000)
  directionLo := (590602937152613131761/100000000000000000000)
  directionHi := (295301468576306565881/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree141.table
  base := (167338784141143322947964977500982969326821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1568392882774490358120533379071438104750000000000)
      constant := (60891225403688545334902542603976446191188039092749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree141.table
  base := (167338784141143318717106812516646220231467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1568803036345773557377886020222110198500000000000)
      constant := (60921837657915278517258942299453928146282541837923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590602937152613131761/100000000000000000000)
  centralHi := (295301468576306565881/50000000000000000000)
  directionLo := (148177120037188432223/25000000000000000000)
  directionHi := (592708480148753728893/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree142.table
  base := (170781554369199053421323984837086312711069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (3438216)
      previous := (1719108)
      next := (1719108)
      square := (18761115109579722697724646460470000000000000)
      linear := (-2819995023967357161428963860023916500000000000)
      constant := (110286308007461750060519525551935788165398535389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree142.table
  base := (170781554369199050062166022607004089624979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (382024)
      previous := (191012)
      next := (191012)
      square := (2084568345508858077524960717830000000000000)
      linear := (-313414721020436521267691147997331000000000000)
      constant := (12260193298340822592777727118867040862756566011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148177120037188432223/25000000000000000000)
  centralHi := (592708480148753728893/100000000000000000000)
  directionLo := (594806569825180805827/100000000000000000000)
  directionHi := (148701642456295201457/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree143.table
  base := (87128983191866077759159215042533830663191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-7157826943334240839221006612559091605125000000000)
      constant := (281971373323453117953098113980636060886372718503511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree143.table
  base := (174257966383732152851393146483639766989897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1591044180982267450042976133886980943500000000000)
      constant := (62691791803805304593171833374552438088541312812593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594806569825180805827/100000000000000000000)
  centralHi := (148701642456295201457/25000000000000000000)
  directionLo := (119379456955399120449/20000000000000000000)
  directionHi := (298448642388497801123/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree144.table
  base := (88884010092373383782630491112493783445313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-800872936528750883673367757325322408000000000000)
      constant := (31777190698726227609004136847448216222035034337897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree144.table
  base := (44442005046186691362005316166924310975901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-400541188325128599093880297679854079000000000000)
      constant := (15896577454630747706529909752763747609627313087269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119379456955399120449/20000000000000000000)
  centralHi := (298448642388497801123/50000000000000000000)
  directionLo := (299490351113813799579/50000000000000000000)
  directionHi := (598980702227627599159/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree145.table
  base := (181311715772246923371264128690813984252999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-14515771828366550133799226038593423477750000000000)
      constant := (580093336456112779297482353244373882044670678871479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree145.table
  base := (90655857886123460845247095328570421685111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-806642662809380671354033123775925844250000000000)
      constant := (32243594230544601254435011205926033004384311543759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299490351113813799579/50000000000000000000)
  centralHi := (598980702227627599159/100000000000000000000)
  directionLo := (300528449031058446787/50000000000000000000)
  directionHi := (24042275922484675743/4000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree146.table
  base := (92444526573118277732073095344893591286119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-7307915399607792180738916222665521805750000000000)
      constant := (294127229142014392039873219799253674015452226546999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree146.table
  base := (36977810629247310825986216153118502399171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1624405897937008289040611304384287061000000000000)
      constant := (65394427731503995327011431969481968565370834099495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300528449031058446787/50000000000000000000)
  centralHi := (24042275922484675743/4000000000000000000)
  directionLo := (75390743357420676941/12500000000000000000)
  directionHi := (603125946859365415529/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree147.table
  base := (471250080766798745576193139836417147143/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-408774715835128294143234412557462881812500000000)
      constant := (16568688835022794443581203229657584797153884091700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree147.table
  base := (47125008076679874292852791130560617661657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-408881617563813808843289090304180608375000000000)
      constant := (16577006907441855894091951008116955517231885440033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75390743357420676941/12500000000000000000)
  centralHi := (603125946859365415529/100000000000000000000)
  directionLo := (302593960961697883793/50000000000000000000)
  directionHi := (605187921923395767587/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree148.table
  base := (192144653253699490957805376807112826330201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-14815948740913652816835045258806283879000000000000)
      constant := (604748355786488703505505563408015627602504663675721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree148.table
  base := (192144653253699490117184495790618471452699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1646647042573502181705701418049157806000000000000)
      constant := (67227988155879540206090941443776282425791893346131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302593960961697883793/50000000000000000000)
  centralHi := (605187921923395767587/100000000000000000000)
  directionLo := (151810723828413688737/25000000000000000000)
  directionHi := (607242895313654754949/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree149.table
  base := (24477864498397522597312759360561470837769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-3729001927940671761128412916385976003187500000000)
      constant := (153270282865258389871397474016600192345365085588298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree149.table
  base := (9791145799359009005564994744014552965307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-414441903722937282009561618720398294625000000000)
      constant := (17038577327460099215089235710810375217264428784415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151810723828413688737/25000000000000000000)
  centralHi := (607242895313654754949/100000000000000000000)
  directionLo := (609290937874397048999/100000000000000000000)
  directionHi := (609290937874397049/100000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree150.table
  base := (49883705126791281378929786420437518164367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-417112963405881146449784946452264559625000000000)
      constant := (17263086807901545036765839668809638019546443998023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree150.table
  base := (39906964101433024997236705498323639770219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1668888187209996074370791531714028551000000000000)
      constant := (69086991091650043918674236417202549538582111035055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609290937874397048999/100000000000000000000)
  centralHi := (609290937874397049/100000000000000000)
  directionLo := (152833029815795720871/25000000000000000000)
  directionHi := (122266423852636576697/20000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree151.table
  base := (12705022925853612277045747378063090527767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-3779031413365188874967716119754786070062500000000)
      constant := (157479584164188832850629540972087439148408136229428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree151.table
  base := (203280366813657796012476274128754049553067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1680008759528243020703336588546463923500000000000)
      constant := (70026033501308530534821741771907056534449553188323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152833029815795720871/25000000000000000000)
  centralHi := (122266423852636576697/20000000000000000000)
  directionLo := (153341626994630553981/25000000000000000000)
  directionHi := (24534660319140888637/4000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree152.table
  base := (103529777453330790443758809447906255330361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-7608092312154894863774735442878382207000000000000)
      constant := (319211383088966560706243238743870426762465563319081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree152.table
  base := (103529777453330790277002232602044531884447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-845564665923244983517940822689449648000000000000)
      constant := (35485718269407952337221852116322155178009657991543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153341626994630553981/25000000000000000000)
  centralHi := (24534660319140888637/4000000000000000000)
  directionLo := (307697085693348196509/50000000000000000000)
  directionHi := (615394171386696393019/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree153.table
  base := (105436192393089892447413226047531650077989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-850902421953267997512670960694132474875000000000)
      constant := (35943578535999411815390188810273653397246156170141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree153.table
  base := (210872384786179784630163263411006328499131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1702249904164736913368426702211334668500000000000)
      constant := (71923200204172213151333476580935110696960961313139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307697085693348196509/50000000000000000000)
  centralHi := (615394171386696393019/100000000000000000000)
  directionLo := (617415175747787033591/100000000000000000000)
  directionHi := (77176896968473379199/12500000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree154.table
  base := (26839857056526954449786132649628321139329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-3854075641501964545726670924808001170375000000000)
      constant := (163900819766731154117055424189624554860306018858818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree154.table
  base := (21471885645221563538827152394501183609839/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-856685238241491929850485879521885020500000000000)
      constant := (36440662248688750831221240851617175224764251513955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617415175747787033591/100000000000000000000)
  centralHi := (77176896968473379199/12500000000000000000)
  directionLo := (309714793120470291163/50000000000000000000)
  directionHi := (619429586240940582327/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree155.table
  base := (5464974247619307091382192788879907369029/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-3879090384214223102646322526492406203812500000000)
      constant := (166069840608684783577662579445883275879784374906090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree155.table
  base := (218598969904772283488640032381890823473521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1724491048801230806033516815876205413500000000000)
      constant := (73845809418431814821653181915817910876027974385049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309714793120470291163/50000000000000000000)
  centralHi := (619429586240940582327/100000000000000000000)
  directionLo := (124287493397779157687/20000000000000000000)
  directionHi := (155359366747223947109/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree156.table
  base := (111256362571926402768716265404386744918497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-867578917094773702125772028483735830500000000000)
      constant := (37389592430635186570807253869187462759593308745993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree156.table
  base := (222512725143852805405204082608590898613591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1735611621119477752366061872708640786000000000000)
      constant := (74816654967335196192356425075189636999730314256879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124287493397779157687/20000000000000000000)
  centralHi := (155359366747223947109/25000000000000000000)
  directionLo := (155859720270450055589/25000000000000000000)
  directionHi := (623438881081800222357/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree157.table
  base := (226460122169460205749537820986279724633317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-15716479478554960865942502919444865082750000000000)
      constant := (681803183017007671258525838817090072201067023255157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree157.table
  base := (113230061084730102822312002150238369172767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-873366096718862349349303464770538079250000000000)
      constant := (37896930572043844159437141537574203890567645917623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155859720270450055589/25000000000000000000)
  centralHi := (623438881081800222357/100000000000000000000)
  directionLo := (156358472650085214289/25000000000000000000)
  directionHi := (625433890600340857157/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree158.table
  base := (230441160981597418970005466686110509310659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-15816538449403995093621109326182485216500000000000)
      constant := (690650920231462447262515307321166329078728794472339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree158.table
  base := (2880514512269967736084590420156656026701/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-439463191438992911257787996593377882750000000000)
      constant := (19194356987172333189192409927311377206852843449380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156358472650085214289/25000000000000000000)
  centralHi := (625433890600340857157/100000000000000000000)
  directionLo := (313711278319106353419/50000000000000000000)
  directionHi := (627422556638212706839/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree159.table
  base := (117227920790133656057750916082715289621063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1870471525402305726024088105835000000000000)
      linear := (-314793667581445143018466748406315125000000000)
      constant := (13835605304275899917936780919822716849198528583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree159.table
  base := (234455841580267312049463572161920198020731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (685576)
      previous := (342788)
      next := (342788)
      square := (3740943050804611452048176211670000000000000)
      linear := (-629751989346464432667745476399411500000000000)
      constant := (27685067775414798897146128188542694311972504971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313711278319106353419/50000000000000000000)
  centralHi := (627422556638212706839/100000000000000000000)
  directionLo := (62940493932394852823/10000000000000000000)
  directionHi := (629404939323948528231/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree160.table
  base := (238504163965472686332770097919100736109139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-16016656391102063548978322139657725484000000000000)
      constant := (708518048507014841405539962576462306201968296160419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree160.table
  base := (238504163965472686280379758505090263900143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1780093910392465537696242100038382276000000000000)
      constant := (78763643441440240019540141165899319657080624004167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62940493932394852823/10000000000000000000)
  centralHi := (629404939323948528231/100000000000000000000)
  directionLo := (315690548921065827023/50000000000000000000)
  directionHi := (631381097842131654047/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree161.table
  base := (48517225627443255784071648853765073387159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-16116715361951097776656928546395345617750000000000)
      constant := (717537439568113165372467030150000696091829261644195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree161.table
  base := (48517225627443255775759375186373960965779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1791214482710712484028787156870817648500000000000)
      constant := (79766292129589581269760064679981210903217919283255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315690548921065827023/50000000000000000000)
  centralHi := (631381097842131654047/100000000000000000000)
  directionLo := (633351090454013129597/100000000000000000000)
  directionHi := (316675545227006564799/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree162.table
  base := (246701734095500765182968922497641596769029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1801863814755570222703948328125885083500000000000)
      constant := (80734894286454818277377907102326025746023054605901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree162.table
  base := (7709429190484398910937483501211330910387/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-450583763757239857590333053425813255250000000000)
      constant := (20193825361397057933879550102729284807341780203224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633351090454013129597/100000000000000000000)
  centralHi := (316675545227006564799/50000000000000000000)
  directionLo := (158828743629388368027/25000000000000000000)
  directionHi := (635314974517553472109/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree163.table
  base := (10034039273613150408842207282907331383671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-16316833303649166232014141359870585885250000000000)
      constant := (735747875536955772049721668302442691568487607589775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree163.table
  base := (125425490920164380097451226023666517519489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-906727813673603188346938635267844196750000000000)
      constant := (40895335694718114223542727735631719621014300033641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158828743629388368027/25000000000000000000)
  centralHi := (635314974517553472109/100000000000000000000)
  directionLo := (127454561301381711519/20000000000000000000)
  directionHi := (159318201626727139399/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree164.table
  base := (15939616960731426291137403548697806187307/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23643695316847845529807485701807317500000000000)
      linear := (-4104223068624550114923186941652051504750000000000)
      constant := (186234730111175178463106596420868648710838209895788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree164.table
  base := (51006774274340564127490762359087914089957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1824576199665453323026422327368123766000000000000)
      constant := (82812401961133607606689002929295482878356361613665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127454561301381711519/20000000000000000000)
  centralHi := (159318201626727139399/25000000000000000000)
  directionLo := (319612321015689181781/50000000000000000000)
  directionHi := (639224642031378363563/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree165.table
  base := (259250402689625446308714655753560472613523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1835216805038581631930150463705091794750000000000)
      constant := (83798575922369834276072661455431109870450794865387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree165.table
  base := (259250402689625446292260377553891885103871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1835696771983700269358967384200559138500000000000)
      constant := (83840493160680404612126144113561575111893145914199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319612321015689181781/50000000000000000000)
  centralHi := (639224642031378363563/100000000000000000000)
  directionLo := (641170535853836554659/100000000000000000000)
  directionHi := (32058526792691827733/5000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree166.table
  base := (131750287897049540893921201332117449516019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47287390633695691059614971403614635000000000000)
      linear := (-8308505108098134457524980290041723143250000000000)
      constant := (381746332053419733745944320263450947581384050224899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree166.table
  base := (65875143948524770443697911346244805321231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2627077257427538392200831744645257500000000000)
      linear := (-461704336075486803922878110258248627750000000000)
      constant := (21218736247019163519891266775662141535064480248039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641170535853836554659/100000000000000000000)
  centralHi := (32058526792691827733/5000000000000000000)
  directionLo := (643110541908658190859/100000000000000000000)
  directionHi := (32155527095432909543/5000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree167.table
  base := (53556878137025223613355146463535314071389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-16717069187045303142728566986821066420250000000000)
      constant := (772855362861233895583136082949406135188126021213345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree167.table
  base := (133892195342563059028212431459879524770193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5254154514855076784401663489290515000000000000)
      linear := (-928968958310097081012028748932714941750000000000)
      constant := (42957878721661194932782273942883539697557494042617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643110541908658190859/100000000000000000000)
  centralHi := (32155527095432909543/5000000000000000000)
  directionLo := (64504471331916216213/10000000000000000000)
  directionHi := (645044713319162162131/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree168.table
  base := (54420369472541778794942572480102831305359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1868569795321593041156352599284298506000000000000)
      constant := (86919475507168010091371851159873974218811870228355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree168.table
  base := (272101847362708893966503633359741428605617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1869058488938441108356602554697865256000000000000)
      constant := (86962930526417645088343354043319438363356971069273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell163.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64504471331916216213/10000000000000000000)
  centralHi := (645044713319162162131/100000000000000000000)
  directionLo := (129394620482916861647/20000000000000000000)
  directionHi := (161743275603646077059/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 95549
  qDenominator := 180624
  table := BinomialMassData.Q95549_180624.Degree169.table
  base := (276452945826849697650003723229544551072663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (94574781267391382119229942807229270000000000000)
      linear := (-16917187128743371598085779800296306687750000000000)
      constant := (791752414216674344813351946545097401465985791740423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95549_180624.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 15929
  qDenominator := 30104
  table := BinomialMassData.Q15929_30104.Degree169.table
  base := (276452945826849697643493250423288632616507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10508309029710153568803326978581030000000000000)
      linear := (-1880179061256688054689147611530300628500000000000)
      constant := (88016464237362452148328849534992291249972401309683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q15929_30104.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell163.Kernel169
