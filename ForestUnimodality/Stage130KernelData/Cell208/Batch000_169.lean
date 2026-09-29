import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell208.Parameters
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch000_049
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch050_099
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch100_149
import ForestUnimodality.BinomialMassData.Q48539_91164.Batch150_199
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch000_049
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch050_099
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch100_149
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree000.table
  base := (54964280906778182581717829/625000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77062536657028050945950071250000000000)
      linear := (-5611851026647014621662190625000000000)
      constant := (109928561813556365163435658000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree000.table
  base := (54964280906778182581717829/625000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77062536657028050945950071250000000000)
      linear := (-5611851026647014621662190625000000000)
      constant := (109928561813556365163435658000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree001.table
  base := (494775435161170848151001467071485433717251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-364322144695669805307654372356958990000000000000)
      constant := (257104243697483982897259236697304171898773331126931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree001.table
  base := (494676643393841140333999483424939099638009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-364409961309317321623109829760651927500000000000)
      constant := (257052978281538250871740823311519760558929480345129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6236723259902918233/12500000000000000000)
  directionHi := (9978757215844669173/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree002.table
  base := (73328890427242254825467602306794157012237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-176331148370653340044762531446269613750000000000)
      constant := (38186191284406757467879401023220049948280178006397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree002.table
  base := (146606166218129812745273980800091708045799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-352750113354954196404980520296232165000000000000)
      constant := (76345669117711973666777016121568026444412007960119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6236723259902918233/12500000000000000000)
  centralHi := (9978757215844669173/20000000000000000000)
  directionLo := (705604689513795867/1000000000000000000)
  directionHi := (70560468951379586701/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree003.table
  base := (92611696124045642005828109223055719476513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-58129280126086495280580326622955440000000000000)
      constant := (5392489181906986864221795529202426438344237175817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree003.table
  base := (46285166241757555270415567446618936075471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-29071958114180540666578118095118798125000000000)
      constant := (2695062909065377361087202813915723855249900661639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (705604689513795867/1000000000000000000)
  centralHi := (70560468951379586701/100000000000000000000)
  directionLo := (43209286235593802063/50000000000000000000)
  directionHi := (86418572471187604127/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree004.table
  base := (25031674048764464756763390616122831737919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-1387329491056500469921841632641317385000000000000)
      constant := (66513133290390540638211202642421792927219708869195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree004.table
  base := (15637188911878135050829004452612374115931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-173460094688886316897957932782011141875000000000)
      constant := (8310285292502749740816217411893567159315696348011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43209286235593802063/50000000000000000000)
  centralHi := (86418572471187604127/100000000000000000000)
  directionLo := (6236723259902918233/6250000000000000000)
  directionHi := (99787572158446691729/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree005.table
  base := (90149835915144308654738690043935137325133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-1728331939843444024793237386069436850000000000000)
      constant := (49158106703407739844862031767105644912360027472573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree005.table
  base := (22526497344796206581861479740655434373473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-432192755727920401592628668271975384375000000000)
      constant := (12284129141866771236717355710487231613974827752113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6236723259902918233/6250000000000000000)
  centralHi := (99787572158446691729/100000000000000000000)
  directionLo := (22313179465595221783/20000000000000000000)
  directionHi := (27891474331994027229/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree006.table
  base := (34247384096576196722237349759753462811111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-114963021590577087759146285527642017500000000000)
      constant := (2162268278489991023598371635226800731846749998399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree006.table
  base := (17115686075041676887949685452894315862157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-57496146897563129932149052331103165000000000000)
      constant := (1080719374897357222964831543837343189287466720213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22313179465595221783/20000000000000000000)
  centralHi := (27891474331994027229/25000000000000000000)
  directionLo := (24442863445935141103/20000000000000000000)
  directionHi := (30553579307418926379/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree007.table
  base := (54179682584265760915988843433290519146347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-2410336837417331134536028892925675780000000000000)
      constant := (32677717886427705932784193058082063254886414525307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree007.table
  base := (54155507446410572455363567745595999953739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-2410951553712863748744217094751526342500000000000)
      constant := (32667474359546320695587505078260000841627913527259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/20000000000000000000)
  centralHi := (30553579307418926379/25000000000000000000)
  directionLo := (132006549933081386287/100000000000000000000)
  directionHi := (8250409370817586643/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree008.table
  base := (1762955804140926794563816799559030123623/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-2751339286204274689407424646353795245000000000000)
      constant := (28802603140611116052328878009286079274572136356575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree008.table
  base := (44054888485486444931193270604888903852213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-2752041819113454819931068305583338745000000000000)
      constant := (28795748935092880509360963717249886823394669734053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132006549933081386287/100000000000000000000)
  centralHi := (8250409370817586643/6250000000000000000)
  directionLo := (141120937902759173401/100000000000000000000)
  directionHi := (70560468951379586701/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree009.table
  base := (4564396819332688894845120196202552058071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-42949190763766920059428061108082148750000000000)
      constant := (367112118824262133554489898390310255307676445039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree009.table
  base := (18249820511030739935250952721515500294143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-171840671361891438395439973134175063750000000000)
      constant := (1468212252097466658020845434128273674206414406487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141120937902759173401/100000000000000000000)
  centralHi := (70560468951379586701/50000000000000000000)
  directionLo := (149681358237670037593/100000000000000000000)
  directionHi := (74840679118835018797/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree010.table
  base := (7648840523314779575682425126889354066641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-858336045944540449787554038302508543750000000000)
      constant := (6273600367944925941352356576876102111381387371521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree010.table
  base := (30582263814065880392410834637880667299193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-3434222349914636962304770727246963550000000000000)
      constant := (25092306086855460327060681629653497078161951547433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149681358237670037593/100000000000000000000)
  centralHi := (74840679118835018797/50000000000000000000)
  directionLo := (39444501274887014787/25000000000000000000)
  directionHi := (157778005099548059149/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree011.table
  base := (12899160820941589023622472413108243254609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-1887173316282552677010805953319076820000000000000)
      constant := (12260746745928044508026538359743568364399454649729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree011.table
  base := (25787029524970861876084191623016942159847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-3775312615315228033491621938078775952500000000000)
      constant := (24521321496499935714498875039328994138216028218807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39444501274887014787/25000000000000000000)
  centralHi := (157778005099548059149/100000000000000000000)
  directionLo := (33095793559008259377/20000000000000000000)
  directionHi := (82739483897520648443/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree012.table
  base := (10907763357487868336847847070700351498389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-228630504519558272716278203337015172500000000000)
      constant := (1364060600089033908932408234855346525321785587101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree012.table
  base := (21805654361620823438258169882037430593039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-457378097857313233853163683212287595000000000000)
      constant := (2728303890483504695170306753963866692555765398951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095793559008259377/20000000000000000000)
  centralHi := (82739483897520648443/50000000000000000000)
  directionLo := (43209286235593802063/25000000000000000000)
  directionHi := (172837144942375208253/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree013.table
  base := (2306425921719601545292539781433742497769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-557043941267374057970550426686799071250000000000)
      constant := (3135951071263199039223255794146726804111669881689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree013.table
  base := (18442708087630574321894320576697391100471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-4457493146116410175865324359742400757500000000000)
      constant := (25091034375066965725109708883906628686131140479751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43209286235593802063/25000000000000000000)
  centralHi := (172837144942375208253/100000000000000000000)
  directionLo := (7195784161426846729/4000000000000000000)
  directionHi := (89947302017835584113/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree014.table
  base := (15574200023342961864487996657760103557253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-4797353978925936018635799166922512035000000000000)
      constant := (26056604875307314716212094537570516435270891026293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree014.table
  base := (7783252997063827786898507355731441369577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-2399291705758500623526087785287106580000000000000)
      constant := (13030909316162003448242859917139967064457084214937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7195784161426846729/4000000000000000000)
  centralHi := (89947302017835584113/50000000000000000000)
  directionLo := (186685453237444879127/100000000000000000000)
  directionHi := (23335681654680609891/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree015.table
  base := (13089975494835558114868636487796188681587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-570928491968097730389688324483403500000000000000)
      constant := (3045698902107796510023364695666253101585282887083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree015.table
  base := (13083163222651376982577426173095676145169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-571074852990843590915447420156225062500000000000)
      constant := (3046480133782411033679919235758990356205077040121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186685453237444879127/100000000000000000000)
  centralHi := (23335681654680609891/12500000000000000000)
  directionLo := (38647560512813493769/20000000000000000000)
  directionHi := (96618901282033734423/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree016.table
  base := (10928559796944984248283775214594803061061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-5479358876499823128378590673778750965000000000000)
      constant := (29115213847184091468878352131369661518264738751541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree016.table
  base := (5461265535062663825824190295804442391317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-2740381971159091694712938996118918982500000000000)
      constant := (14562052385879249557185584387432950734704666479877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38647560512813493769/20000000000000000000)
  centralHi := (96618901282033734423/50000000000000000000)
  directionLo := (199575144316893383457/100000000000000000000)
  directionHi := (99787572158446691729/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree017.table
  base := (9035624548221678800658568772117922128941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-5820361325286766683249986427206870430000000000000)
      constant := (31140156286103491323342014935343793212693664497821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree017.table
  base := (1806059259390881315326439466479372409111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-5821854207718774460612729203069650367500000000000)
      constant := (31150957426757446446374728537831810342254891117955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199575144316893383457/100000000000000000000)
  centralHi := (99787572158446691729/50000000000000000000)
  directionLo := (205717350066609896307/100000000000000000000)
  directionHi := (51429337516652474077/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree018.table
  base := (3684015759091859169978864959655729162141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-342297987448539457673410121146388327500000000000)
      constant := (1859095008801679899390708680030809899557032989669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree018.table
  base := (736333056371631205566332949383458583137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-342385804062186973988865578550081265000000000000)
      constant := (1859804279413908633435787459929278678446146605165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205717350066609896307/100000000000000000000)
  centralHi := (51429337516652474077/25000000000000000000)
  directionLo := (211681406854138760101/100000000000000000000)
  directionHi := (105840703427069380051/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree019.table
  base := (2945467800751785732117445286458940177247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-3251183111430326896496388967031554680000000000000)
      constant := (18033887941109820514660045647203487768052992668207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree019.table
  base := (1471699003012679974633797581366500654311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-1626008684629989150746607906183318793125000000000)
      constant := (9020641940545599900900978829415826148212866504791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211681406854138760101/100000000000000000000)
  centralHi := (105840703427069380051/50000000000000000000)
  directionLo := (217481971429971007103/100000000000000000000)
  directionHi := (1699077901796648493/781250000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree020.table
  base := (4575870860953775084904932128708061704883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-6843368671647597347864173687491228825000000000000)
      constant := (38937567404778272667660977198959084808495692832323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree020.table
  base := (1143058159710354522164453357723559155267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-1711281250980136918543320708891271893750000000000)
      constant := (9738611663653416509487064675389881686954967279827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217481971429971007103/100000000000000000000)
  centralHi := (1699077901796648493/781250000000000000)
  directionLo := (223131794655952217831/100000000000000000000)
  directionHi := (27891474331994027229/12500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree021.table
  base := (212463207263656386952445149803052797831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-99782932228257512537994020012768726250000000000)
      constant := (584179396897549594453075069657103298729600293758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree021.table
  base := (3396219727722504717540451175319577138603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-798468363257904305040014894044099997500000000000)
      constant := (4675549810168158088585840466113351605215633230627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223131794655952217831/100000000000000000000)
  centralHi := (27891474331994027229/12500000000000000000)
  directionLo := (22864205141597493997/10000000000000000000)
  directionHi := (228642051415974939971/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree022.table
  base := (468437286754471631814009245140002513989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-7525373569221484457606965194347467755000000000000)
      constant := (45427761767705639893170979400652989110902521537545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree022.table
  base := (2339391623495356464518795014310312591843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-7527305534721729816546985257228712380000000000000)
      constant := (45449013576779492978485009302725479418966292692083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22864205141597493997/10000000000000000000)
  centralHi := (228642051415974939971/100000000000000000000)
  directionLo := (23402260054324802197/10000000000000000000)
  directionHi := (234022600543248021971/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree023.table
  base := (347032206368479395556518132143031200591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-1966594004502107003119590236943896805000000000000)
      constant := (12257439274931919040924168647093740071489780141471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree023.table
  base := (692842769038578018330576450773655224379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-3934197900061160443866918234030262391250000000000)
      constant := (24526649510761024096768400835132843714293792393099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23402260054324802197/10000000000000000000)
  centralHi := (234022600543248021971/100000000000000000000)
  directionLo := (47856438419232131873/20000000000000000000)
  directionHi := (119641096048080329683/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree024.table
  base := (523882972391916444567557369856743163499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-911930940755041285261084077911522965000000000000)
      constant := (5873329479972402631485366275283408376346135157091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree024.table
  base := (521750300693394370568009933163288636121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-912165118391434662102298630988037465000000000000)
      constant := (5876207736818300964077191388396695609130139567489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47856438419232131873/20000000000000000000)
  centralHi := (119641096048080329683/50000000000000000000)
  directionLo := (24442863445935141103/10000000000000000000)
  directionHi := (244428634459351411031/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree025.table
  base := (-26166862309978666279979711080358809293/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-4274190457791157561110576227315913075000000000000)
      constant := (28456305834766008781451494683927839315054485872335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree025.table
  base := (-32940936929449227005758961093349032351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-1068822041365437878763442361215518698437500000000)
      constant := (7117619096621136206636808984041005186158167639969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/10000000000000000000)
  centralHi := (244428634459351411031/100000000000000000000)
  directionLo := (124734465198058364661/50000000000000000000)
  directionHi := (249468930396116729323/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree026.table
  base := (-122223769294985577734678647767629410407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-1111172920546157334636568526007493201875000000000)
      constant := (7647860506508478705003221942227653573851073909833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree026.table
  base := (-979408223509845041896608179862901235087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-8891666596324094101294390100555961990000000000000)
      constant := (61213738333637955204631298682878056954599253582753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124734465198058364661/50000000000000000000)
  centralHi := (249468930396116729323/100000000000000000000)
  directionLo := (63602347206245970987/25000000000000000000)
  directionHi := (254409388824983883949/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree027.table
  base := (-1632207550631339908569397820163551533991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1025598423684022470218215995720896120000000000000)
      constant := (7296307710044106593820315494103814169249666023681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree027.table
  base := (-163361427419560182489576489432976397019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-512930936762482509582291183965987466250000000000)
      constant := (3650011948580610089042080560627647777316120266145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63602347206245970987/25000000000000000000)
  centralHi := (254409388824983883949/100000000000000000000)
  directionLo := (129627858706781406189/50000000000000000000)
  directionHi := (259255717413562812379/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree028.table
  base := (-34865123678315766424312509821310704069/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-1196423532742893223354417464364523068125000000000)
      constant := (8795114858450754648671197329040473349993431424088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree028.table
  base := (-1116294749352976174179369025245152807137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-4786923563562638121834046261109793397500000000000)
      constant := (35198517933914071494694322101720289320592573566703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129627858706781406189/50000000000000000000)
  centralHi := (259255717413562812379/100000000000000000000)
  directionLo := (10560523994646510903/4000000000000000000)
  directionHi := (8250409370817586643/3125000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree029.table
  base := (-2780653974610146764555603831397118596481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-9912390710730089341706735468344304010000000000000)
      constant := (75262536536093939650957800185187500269985706447439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree029.table
  base := (-2781713654995911899634225907417149919301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-9914937392525867314854943733051399197500000000000)
      constant := (75301406307811008561467223346831464591769555827019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10560523994646510903/4000000000000000000)
  centralHi := (8250409370817586643/3125000000000000000)
  directionLo := (268686260888530991403/100000000000000000000)
  directionHi := (67171565222132747851/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree030.table
  base := (-410570223050917687875569684808623973423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-142408238326625456896918489191283659375000000000)
      constant := (1116240097372669368090022690285424145520659847993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree030.table
  base := (-1642740053943610870683717444563609106283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-569779314329247688113433052437956200000000000000)
      constant := (4467277355963533590726269485136892092211358468253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268686260888530991403/100000000000000000000)
  centralHi := (67171565222132747851/25000000000000000000)
  directionLo := (136639760574639327851/50000000000000000000)
  directionHi := (273279521149278655703/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree031.table
  base := (-3746848253191796470206893899994097936257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-10594395608303976451449526975200542940000000000000)
      constant := (85679218842095275015614115646715848561462268155983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree031.table
  base := (-1873821669408462373742941666424129074279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-5298558961663524728614323077357512001250000000000)
      constant := (42861921988665383801309016146655249228385058725001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136639760574639327851/50000000000000000000)
  centralHi := (273279521149278655703/100000000000000000000)
  directionLo := (55559368811712877993/20000000000000000000)
  directionHi := (138898422029282194983/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree032.table
  base := (-41706537621046082637220438172366871419/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-2733849514272730001580230682157165601250000000000)
      constant := (22797675205677210742173691386398885294096520316525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree032.table
  base := (-1042835387777902377669271930696120899043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-2734552047181910132103874341386709101250000000000)
      constant := (22809582735454913604646213102324587658472661304717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55559368811712877993/20000000000000000000)
  centralHi := (138898422029282194983/50000000000000000000)
  directionLo := (141120937902759173401/50000000000000000000)
  directionHi := (282241875805518346803/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree033.table
  base := (-1139651046756272859934855938209345488173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-313233347385496210033119957834910607500000000000)
      constant := (2691732472077848900202873838812729679842028815243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree033.table
  base := (-911839734958560281365517098261644339303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1253255383792025733289149841819849867500000000000)
      constant := (10772565594852913092427017983303988581225909415365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141120937902759173401/50000000000000000000)
  centralHi := (282241875805518346803/100000000000000000000)
  directionLo := (286617979805065516203/100000000000000000000)
  directionHi := (71654494951266379051/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree034.table
  base := (-4912895848395370399476269672840984906413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-11617402954664807116063714235484901335000000000000)
      constant := (102813082524349800874753608712159651841336080555747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree034.table
  base := (-4913409298273446982659712334525444170603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-11620388719528822670789199787210461210000000000000)
      constant := (102866982278541194721358926188419900414955374132357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286617979805065516203/100000000000000000000)
  centralHi := (71654494951266379051/25000000000000000000)
  directionLo := (290928266479653443483/100000000000000000000)
  directionHi := (72732066619913360871/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree035.table
  base := (-5235366291613924847902840038686239718423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-11958405403451750670935109988913020800000000000000)
      constant := (108921886935730409040007541623187013828345011286937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree035.table
  base := (-5235809430410305458120227403283136907063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-11961478984929413741976050998042273612500000000000)
      constant := (108979053038919805470821391482642079425716189263097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290928266479653443483/100000000000000000000)
  centralHi := (72732066619913360871/25000000000000000000)
  directionLo := (36896952390698786791/12500000000000000000)
  directionHi := (295175619125590294329/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree036.table
  base := (-690944161811817829048976451332628893031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-170825109058870753136201468643626948125000000000)
      constant := (1600388659187571113945872093786498680397391616321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree036.table
  base := (-552793548994782578048492229394314359289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-683476069462778045175716789381893667500000000000)
      constant := (6404916920739652141279239304693428946467108523995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36896952390698786791/12500000000000000000)
  centralHi := (295175619125590294329/100000000000000000000)
  directionLo := (149681358237670037593/50000000000000000000)
  directionHi := (299362716475340075187/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree037.table
  base := (-1447686021126216408297295730929036504939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-3160102575256409445169475373942314932500000000000)
      constant := (30432675869380260676840234219986592691320930305541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree037.table
  base := (-5791073505444770237935262172243527735663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-12643659515730595884349753419705898417500000000000)
      constant := (121794668880318959152868745672786890789731165586497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149681358237670037593/50000000000000000000)
  centralHi := (299362716475340075187/100000000000000000000)
  directionLo := (75873013114353672273/25000000000000000000)
  directionHi := (303492052457414689093/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree038.table
  base := (-3013008204346903347305961768178626712179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-6490706374906290667774648624598689597500000000000)
      constant := (64214743584986180529830806922240550315874783215101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree038.table
  base := (-3013150084420708204881791645601445353263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-6492374890565593477768302315268855410000000000000)
      constant := (64248493347092196823142717810953700644203167600897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75873013114353672273/25000000000000000000)
  centralHi := (303492052457414689093/100000000000000000000)
  directionLo := (19222872097993936141/6250000000000000000)
  directionHi := (307565953567902978257/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree039.table
  base := (-6234272819264305236545920113674686299747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1480268355399947210046743666958388740000000000000)
      constant := (15035985080717357398985685608820229901324705045477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree039.table
  base := (-3117258552886722535781300330773355552869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-740324447029543223706858657853862401250000000000)
      constant := (7521943871321873274210690043772122533584922410579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19222872097993936141/6250000000000000000)
  centralHi := (307565953567902978257/100000000000000000000)
  directionLo := (12463463767890706367/4000000000000000000)
  directionHi := (38948324274658457397/12500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree040.table
  base := (-6416269306579017277526527227277969904937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-13663417647386468445292088756053618125000000000000)
      constant := (142413446463139695810969057472296248843950973764903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree040.table
  base := (-6416479494495549424423147622239530585893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-13666930311932369097910307052201335625000000000000)
      constant := (142488285587147001595194220757476786997179855909867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12463463767890706367/4000000000000000000)
  centralHi := (38948324274658457397/12500000000000000000)
  directionLo := (39444501274887014787/12500000000000000000)
  directionHi := (315556010199096118297/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree041.table
  base := (-3286319610089903973928286756167640604673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-7002210048086706000081742254740868795000000000000)
      constant := (74848950199736153109588526555930284141629556500687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree041.table
  base := (-205400624188024887239772663165144715761/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-1751002572166620021137144782879143503437500000000)
      constant := (18722068224095696729549897525343954392022618641036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39444501274887014787/12500000000000000000)
  centralHi := (315556010199096118297/100000000000000000000)
  directionLo := (319476110941164667809/100000000000000000000)
  directionHi := (31947611094116466781/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree042.table
  base := (-6703913260043983547923986816874000822449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1593935838328928395003875584767761895000000000000)
      constant := (17464105763792680988516151762191460960066842032359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree042.table
  base := (-6704068623653243767534205252803314244301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1594345649192616804476001052651662270000000000000)
      constant := (17473277217968821229019616576088713817023886166891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319476110941164667809/100000000000000000000)
  centralHi := (31947611094116466781/10000000000000000000)
  directionLo := (323348690041278280889/100000000000000000000)
  directionHi := (32334869004127828089/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree043.table
  base := (-6810536189010241381740924154866209130857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-14686424993747299109906276016337976520000000000000)
      constant := (164850369864105738648295400977994559657854661233383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree043.table
  base := (-340533483244343959184029300659333068351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-3672550277033535577867715171174193208125000000000)
      constant := (41234225588046442771690119175552298029301256869845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323348690041278280889/100000000000000000000)
  centralHi := (32334869004127828089/10000000000000000000)
  directionLo := (65435086991836408023/20000000000000000000)
  directionHi := (81793858739795510029/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree044.table
  base := (-430805050522648555780804883372189582927/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-1878428430316780333097208971220761998125000000000)
      constant := (21589745090666902152075508052207359201962410687426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree044.table
  base := (-1378599085491549088652091354553807266471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-15031291373534733382657711895528585235000000000000)
      constant := (172808574565046616666985145234694136941207432371245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65435086991836408023/20000000000000000000)
  centralHi := (81793858739795510029/25000000000000000000)
  directionLo := (33095793559008259377/10000000000000000000)
  directionHi := (330957935590082593771/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree045.table
  base := (-6951259648085981954150413875694127576427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1707603321257909579961007502577135050000000000000)
      constant := (20086618013385760631097625926026416634030913363357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree045.table
  base := (-868919753891619118399752288962440008459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-213505300540768395192285598699449967187500000000)
      constant := (2512143742722650886833426598136673202592740064269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095793559008259377/10000000000000000000)
  centralHi := (330957935590082593771/100000000000000000000)
  directionLo := (167348845991964163373/50000000000000000000)
  directionHi := (334697691983928326747/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree046.table
  base := (-6985934748128523995024110214945592901687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-15709432340108129774520463276622334915000000000000)
      constant := (189035037938189301775073853394613415116720857228153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree046.table
  base := (-1746504789851541836707575415906430260691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-3928367976083978881257853579298052510000000000000)
      constant := (47283522789741218731757633735588378879934277030429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167348845991964163373/50000000000000000000)
  centralHi := (334697691983928326747/100000000000000000000)
  directionLo := (169198060648377306871/50000000000000000000)
  directionHi := (338396121296754613743/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree047.table
  base := (-3498562922236634821193383173496916249809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-8025217394447536664695929515025227190000000000000)
      constant := (98742137020547946548323734306401117795065494819071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree047.table
  base := (-3498599119429823940806578938926572354597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-8027281084868253298109132764012011221250000000000)
      constant := (98793842818584512027523374770054498886068886406443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169198060648377306871/50000000000000000000)
  centralHi := (338396121296754613743/100000000000000000000)
  directionLo := (534460256352270477/156250000000000000)
  directionHi := (342054564065453105281/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree048.table
  base := (-3492508610909213390285963837066056294763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-910635402093445382459069710193254102500000000000)
      constant := (11451509705902756463442690033494000176987023659933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree048.table
  base := (-218283727684463617700274719458508528799/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-227717394932459689825071065817442150625000000000)
      constant := (2864375518431367450283767107513304029705624940836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534460256352270477/156250000000000000)
  centralHi := (342054564065453105281/100000000000000000000)
  directionLo := (69134857976950083301/20000000000000000000)
  directionHi := (172837144942375208253/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree049.table
  base := (-347488172567349434661186726206407646119/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-4183109921617240109783662634226673327500000000000)
      constant := (53740914911197549379272072759227773947820984709805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree049.table
  base := (-3474908319649196710741428443635669359757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-8368371350268844369295983974843823623750000000000)
      constant := (107538033030249458173757352011533172741505572252483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69134857976950083301/20000000000000000000)
  centralHi := (172837144942375208253/50000000000000000000)
  directionLo := (349256502554563421051/100000000000000000000)
  directionHi := (87314125638640855263/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree050.table
  base := (-5513195356801475850097071927859926893/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-8536721067627951997003023145167406387500000000000)
      constant := (111996830752968287021490024181224154163303555541875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree050.table
  base := (-861442470102453315441039925015232696829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-2134729120742284976222352395064932456250000000000)
      constant := (28013838073900349246792131374765486953504717818451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349256502554563421051/100000000000000000000)
  centralHi := (87314125638640855263/25000000000000000000)
  directionLo := (352802344756897933503/100000000000000000000)
  directionHi := (5512536636826530211/1562500000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree051.table
  base := (-1702579558905317095759033613628868138063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-483734571778967987468817834548970340000000000000)
      constant := (6478253438505890344910582474183892177416513550233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree051.table
  base := (-272414290253136584619609271631602851137/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-1935435914593207875662852263483474672500000000000)
      constant := (25926544056229099831093988651840992673879076674175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352802344756897933503/100000000000000000000)
  centralHi := (5512536636826530211/1562500000000000000)
  directionLo := (35631290231380110399/10000000000000000000)
  directionHi := (356312902313801103991/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree052.table
  base := (-6706326839228376737108409747470160571737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-17755447032829791103748837797191051705000000000000)
      constant := (242633999077777069620772135613464862792203872474103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree052.table
  base := (-6706360244506268374784140545416483177349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-17760013496739461952152521582183084455000000000000)
      constant := (242760594475328559632273193412664821986047742504331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35631290231380110399/10000000000000000000)
  centralHi := (356312902313801103991/100000000000000000000)
  directionLo := (7195784161426846729/2000000000000000000)
  directionHi := (359789208071342336451/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree053.table
  base := (-6579596590864354045669361648693911043309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-18096449481616734658620233550619171170000000000000)
      constant := (252244247600607543670236450420571655747006628945571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree053.table
  base := (-6579625179572447187899600073959973051779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-18101103762140053023339372793014896857500000000000)
      constant := (252375758786412056424438412679414477321727087547501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7195784161426846729/2000000000000000000)
  centralHi := (359789208071342336451/100000000000000000000)
  directionLo := (90808061362250134069/25000000000000000000)
  directionHi := (363232245449000536277/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree054.table
  base := (-6430191757912059661416761991864351823279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2048605770044853134832403256005254515000000000000)
      constant := (29116426219146366358526027042106949106351380072889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree054.table
  base := (-321510810844248349768267658623922680811/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-512283167431684558181284000106853035000000000000)
      constant := (7282898780975423338765549884025846955920237471505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90808061362250134069/25000000000000000000)
  centralHi := (363232245449000536277/100000000000000000000)
  directionLo := (73328590337805423309/20000000000000000000)
  directionHi := (183321475844513558273/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree055.table
  base := (-6258166276295423144081790682014751936843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-18778454379190621768363025057475410100000000000000)
      constant := (272044736176986569118787877264812480198526508362917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree055.table
  base := (-156454679894099819148509415870822797777/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-2347910536617654395714134401834815207812500000000)
      constant := (34023294811962151549880936570911405750438483154315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73328590337805423309/20000000000000000000)
  centralHi := (183321475844513558273/50000000000000000000)
  directionLo := (370022220836210826433/100000000000000000000)
  directionHi := (185011110418105413217/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree056.table
  base := (-6063565414780018474286762043591671402463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-19119456827977565323234420810903529565000000000000)
      constant := (282234924700674897989860803167092463299161821295697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree056.table
  base := (-1515895825430433453390791490426290961033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-4781093639585456559224981606377583516250000000000)
      constant := (70595435614365445082339300333739413293347445379527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370022220836210826433/100000000000000000000)
  centralHi := (185011110418105413217/50000000000000000000)
  directionLo := (186685453237444879127/50000000000000000000)
  directionHi := (74674181294977951651/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree057.table
  base := (-5846427170441818431015736230679896660751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2162273252973834319789535173814627670000000000000)
      constant := (32513153534063692485177849690653491087918682538841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree057.table
  base := (-5846442460128900180212515946089109850039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2162829424860268589787419737371349607500000000000)
      constant := (32530054255649526029182264459982269909450170488049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186685453237444879127/50000000000000000000)
  centralHi := (74674181294977951651/20000000000000000000)
  directionLo := (188344912123476391069/50000000000000000000)
  directionHi := (376689824246952782139/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree058.table
  base := (-5606783438882006799945985923065773089829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-19801461725551452432977212317759768495000000000000)
      constant := (303195090927159624051990691294167913146931738185451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree058.table
  base := (-5606796504862661138397571636254695247523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-19806555089143008379273628847173958870000000000000)
      constant := (303352579490388411170494601699933986739701912069837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188344912123476391069/50000000000000000000)
  centralHi := (376689824246952782139/100000000000000000000)
  directionLo := (379979754171876211919/100000000000000000000)
  directionHi := (4749746927148452649/1250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree059.table
  base := (-668082624458662383350842333130192340309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-2517808021792299498481076008898485995000000000000)
      constant := (39245629769301119570962355335780476599251527688571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree059.table
  base := (-5344672158388292272507660996198287451713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-20147645354543599450460480058005771272500000000000)
      constant := (314128002145648197422543428811095313225741663506447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379979754171876211919/100000000000000000000)
  centralHi := (4749746927148452649/1250000000000000000)
  directionLo := (191620721393746179329/50000000000000000000)
  directionHi := (383241442787492358659/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree060.table
  base := (-1265020579889303436373633162955184799963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-568985183975703876186666772906000206250000000000)
      constant := (9025783661449707236511784124732361972034352233133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree060.table
  base := (-5060091853796030942377145569859465673169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2276526179993798946849703474315287075000000000000)
      constant := (36121860512690243020305979649301911725617264007879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191620721393746179329/50000000000000000000)
  centralHi := (383241442787492358659/100000000000000000000)
  directionLo := (386475605128134937691/100000000000000000000)
  directionHi := (96618901282033734423/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree061.table
  base := (-4753066283060317138823393089445265488481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-20824469071912283097591399578044126890000000000000)
      constant := (336084602097556915049642810191431269047233004995439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree061.table
  base := (-4753074424354262888128923925957827368839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-20829825885344781592834182479669396077500000000000)
      constant := (336258797113521790658748779693454286568632138889641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386475605128134937691/100000000000000000000)
  centralHi := (96618901282033734423/25000000000000000000)
  directionLo := (194841463277505040839/50000000000000000000)
  directionHi := (389682926555010081679/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree062.table
  base := (-2211814365910378439380284911012578324423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-10582735760349613326231397665736123177500000000000)
      constant := (173717100389907237094363466900234574818957446600937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree062.table
  base := (-4423635681990174260703491605654824855911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-21170916150745372664021033690501208480000000000000)
      constant := (347614151430392713552917677911379140793358278305609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194841463277505040839/50000000000000000000)
  centralHi := (389682926555010081679/100000000000000000000)
  directionLo := (39286406445206550963/10000000000000000000)
  directionHi := (392864064452065509631/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree063.table
  base := (-2035891485360547940175461502532213700649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1194804109415898344851899504716686990000000000000)
      constant := (19943166719333957363014023194789756222492840048559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree063.table
  base := (-1017947225659033668529328892759930948543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-597555733781832325977996802814806135625000000000)
      constant := (9976744463025323337196606803739630606931843843913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39286406445206550963/10000000000000000000)
  centralHi := (392864064452065509631/100000000000000000000)
  directionLo := (396019649799244158863/100000000000000000000)
  directionHi := (24751228112452759929/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree064.table
  base := (-3697540171790355623179486141032481704847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-21847476418273113762205586838328485285000000000000)
      constant := (370712996799063719336336259344108660937412986636193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree064.table
  base := (-3697545233473146294279458117650012765361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-21853096681546554806394736112164833285000000000000)
      constant := (370904739038901898412930827460016804319642607920159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396019649799244158863/100000000000000000000)
  centralHi := (24751228112452759929/6250000000000000000)
  directionLo := (79830057726757353383/20000000000000000000)
  directionHi := (99787572158446691729/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree065.table
  base := (-825227429128618687549642568916074917733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-5547119716765014329269245647939151187500000000000)
      constant := (95660545864987421544921041872362349826428596566827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree065.table
  base := (-825228508667230497403211921553080758593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-5548546736736786469395396830749161421875000000000)
      constant := (95709990419603639793183027198624246679379612501167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79830057726757353383/20000000000000000000)
  centralHi := (99787572158446691729/25000000000000000000)
  directionLo := (402256563409168734507/100000000000000000000)
  directionHi := (100564140852292183627/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree066.table
  base := (-1440949741561305398621868072301350274469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1251637850880388937330465463621373567500000000000)
      constant := (21931364268804615273364351697825930676507033876179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree066.table
  base := (-1440951583085044326358881242509590049711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1251959845130429830487135474101581005000000000000)
      constant := (21942692472486669629701794731545700609386149014201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402256563409168734507/100000000000000000000)
  centralHi := (100564140852292183627/25000000000000000000)
  directionLo := (16213561370412060739/4000000000000000000)
  directionHi := (101334758565075379619/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree067.table
  base := (-2440516087712155361173537570174859385923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-22870483764633944426819774098612843680000000000000)
      constant := (407080113498066527976870429344307984339325160219437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree067.table
  base := (-2440519228400966737644183850311253892989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-22876367477748328019955289744660270492500000000000)
      constant := (407290244089482081660542459616454232151685965593491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16213561370412060739/4000000000000000000)
  centralHi := (101334758565075379619/25000000000000000000)
  directionLo := (81679648036556374353/20000000000000000000)
  directionHi := (204199120091390935883/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree068.table
  base := (-395353017328787771372227401435737395489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-23211486213420887981691169852040963145000000000000)
      constant := (419588850552561311685327799410416240068306889454955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree068.table
  base := (-1976767764291316349466898772012855495441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-23217457743148919091142140955492082895000000000000)
      constant := (419805297553418407053677049053072515147103984415679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81679648036556374353/20000000000000000000)
  centralHi := (204199120091390935883/50000000000000000000)
  directionLo := (205717350066609896307/50000000000000000000)
  directionHi := (82286940026643958523/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree069.table
  base := (-59626045857587706872167440002828364171/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2616943184689759059618062845052120290000000000000)
      constant := (48032307286448614636861649803245034317710849001525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree069.table
  base := (-372663357214301232088749148254858263407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-654404111348597504509138671286774869375000000000)
      constant := (12014267291072653293158737689284354936331511168537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205717350066609896307/50000000000000000000)
  centralHi := (82286940026643958523/20000000000000000000)
  directionLo := (103612228514251574371/25000000000000000000)
  directionHi := (82889782811401259497/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree070.table
  base := (-491089093204322835113999737175924293069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-11946745555497387545716980679448601037500000000000)
      constant := (222592928269344822813425514078398853803571018819011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree070.table
  base := (-245545032888747646836206302530222535997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-5974909568487525308378960844288926925000000000000)
      constant := (111353804208596436795644687692628104823861817273043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103612228514251574371/25000000000000000000)
  centralHi := (82889782811401259497/20000000000000000000)
  directionLo := (417441363849284937517/100000000000000000000)
  directionHi := (208720681924642468759/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree071.table
  base := (-451349498387574921898842026154703644841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (18135216)
      previous := (9067608)
      next := (9067608)
      square := (63524806717414619180173130333370000000000000)
      linear := (-4807477397298496061556309683063940000000000000)
      constant := (90909367531172371821701950729907297556731938519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree071.table
  base := (-90270231157352122612867394483878350621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (18135216)
      previous := (9067608)
      next := (9067608)
      square := (63524806717414619180173130333370000000000000)
      linear := (-4808714251011841361773992181707502500000000000)
      constant := (90956175146842411058568204337933366735618307695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417441363849284937517/100000000000000000000)
  centralHi := (208720681924642468759/50000000000000000000)
  directionLo := (210206257127178777781/50000000000000000000)
  directionHi := (420412514254357555563/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree072.table
  base := (101832152727712060730304877646097912759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2730610667618740244575194762861493445000000000000)
      constant := (52395062188857714068485500995151405222191019244431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree072.table
  base := (25457685192497086599279043829052428271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-682828300131980093774709605522759236250000000000)
      constant := (13105505758020458807219712149030494731677675656839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210206257127178777781/50000000000000000000)
  centralHi := (420412514254357555563/100000000000000000000)
  directionLo := (423362813708277520203/100000000000000000000)
  directionHi := (105840703427069380051/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree073.table
  base := (677364444573719655624203125536715968027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-24916498457355605756048148619181560470000000000000)
      constant := (485030169257623616719362293834474911255934870809387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree073.table
  base := (67736324192718548923655917126075973247/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-12461454535075937223538198504825572453750000000000)
      constant := (242639800375900342585497387551012374941342893721035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423362813708277520203/100000000000000000000)
  centralHi := (105840703427069380051/25000000000000000000)
  directionLo := (2664329344555974787/625000000000000000)
  directionHi := (426292695128955965921/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree074.table
  base := (318811356611077895090572004639304546883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-6314375226535637327729886093152419983750000000000)
      constant := (124674487346274457642064412108594715267099286234323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree074.table
  base := (1275244402260316334508397425255597944379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-25263999335552465518263248220482957310000000000000)
      constant := (498954258293913863513080280501981481650588039713099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2664329344555974787/625000000000000000)
  centralHi := (426292695128955965921/100000000000000000000)
  directionLo := (85840515331544532579/20000000000000000000)
  directionHi := (26825161041107666431/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree075.table
  base := (379094691955369314488899070800622211393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2844278150547721429532326680670866600000000000000)
      constant := (56950988803447110901506414127198242448189100308685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree075.table
  base := (473868146930651685425626446352498352677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-711252488915362683040280539758743603125000000000)
      constant := (14245060529619546040424498057779203520168539122893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85840515331544532579/20000000000000000000)
  centralHi := (26825161041107666431/6250000000000000000)
  directionLo := (432092862355938020631/100000000000000000000)
  directionHi := (54011607794492252579/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree076.table
  base := (507609433635226695539763620316809100989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-25939505803716436420662335879465918865000000000000)
      constant := (526613018080461604284116942534817400796323065272545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree076.table
  base := (2538046425778910737985185971065888480259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-25946179866353647660636950642146582115000000000000)
      constant := (526883362356034573963642281272261821753282507167379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432092862355938020631/100000000000000000000)
  centralHi := (54011607794492252579/12500000000000000000)
  directionLo := (217481971429971007103/50000000000000000000)
  directionHi := (434963942859942014207/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree077.table
  base := (3202965395445990488188488744132294354803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-26280508252503379975533731632894038330000000000000)
      constant := (540860305332848035190020696184864922805388423107843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree077.table
  base := (3202964763531609592688889437090441235497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-26287270131754238731823801852978394517500000000000)
      constant := (541137807564257370715231064420762600552384702586457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217481971429971007103/50000000000000000000)
  centralHi := (434963942859942014207/100000000000000000000)
  directionLo := (218908097998672837389/50000000000000000000)
  directionHi := (437816195997345674779/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree078.table
  base := (3890227170344049266030815342015361082059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2957945633476702614489458598480239755000000000000)
      constant := (61700084498187908585759786800589129903772635688131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree078.table
  base := (3890226632556341428176269919786419257713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-2958706710794981089223405895978911880000000000000)
      constant := (61731723798660410038590950191346096423060124486617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218908097998672837389/50000000000000000000)
  centralHi := (437816195997345674779/100000000000000000000)
  directionLo := (440649987367417842517/100000000000000000000)
  directionHi := (220324993683708921259/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree079.table
  base := (4599831676981724629483126053252980690509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-26962513150077267085276523139750277260000000000000)
      constant := (569934383109194282997075174537161648326745249597629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree079.table
  base := (2299915609685681051504804230142074707723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-13484725331277710437098752137321009661250000000000)
      constant := (285113240902273485000597064968072648541751351126363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440649987367417842517/100000000000000000000)
  centralHi := (220324993683708921259/50000000000000000000)
  directionLo := (443465670888091184983/100000000000000000000)
  directionHi := (55433208861011398123/12500000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree080.table
  base := (1066355645992872178575855460913682801313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-27303515598864210640147918893178396725000000000000)
      constant := (584761172853343025003821574951676023630105989855765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree080.table
  base := (1332944460159292465546991087233522123737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-6827635231989002986346088871368457931250000000000)
      constant := (146265177514780097566389680068835178131739152437897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443465670888091184983/100000000000000000000)
  centralHi := (55433208861011398123/12500000000000000000)
  directionLo := (223131794655952217831/50000000000000000000)
  directionHi := (446263589311904435663/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree081.table
  base := (760758281688977425100040582508708071171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-383951639550710474930823814536201613750000000000)
      constant := (8330293464125834854779961822488238755165539202939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree081.table
  base := (6086065922328055757524364857975010912151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3072403465928511446285689632922849347500000000000)
      constant := (66676466517055328917295190885262711209844595883759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223131794655952217831/50000000000000000000)
  centralHi := (446263589311904435663/100000000000000000000)
  directionLo := (449044074713010112779/100000000000000000000)
  directionHi := (22452203735650505639/5000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree082.table
  base := (3431347631960837485782689799462894050911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-13992760248219048874945355200017317827500000000000)
      constant := (307497126274548070103517666185710684655701498489391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree082.table
  base := (857836872779868911442440351956182748521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-3499090182344649260969757238392182066250000000000)
      constant := (76913618417151006883157413446560374409401341251801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449044074713010112779/100000000000000000000)
  centralHi := (22452203735650505639/5000000000000000000)
  directionLo := (451807448947206612493/100000000000000000000)
  directionHi := (225903724473603306247/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree083.table
  base := (7661664854839503318449565208250623724069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-28326522945225041304762106153462755120000000000000)
      constant := (630400542038378568012263663058855837113419192691989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree083.table
  base := (61293316922344733092446753861338914083/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-28333811724157785158944909117969268932500000000000)
      constant := (630722955899841779959413896473992033333908637190375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451807448947206612493/100000000000000000000)
  centralHi := (225903724473603306247/50000000000000000000)
  directionLo := (454554024086798741951/100000000000000000000)
  directionHi := (7102406626356230343/1562500000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree084.table
  base := (8482974684886620931776255743493758913999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3185280599334664984403722434098986065000000000000)
      constant := (71777777523065019142690105906423153945909934111591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree084.table
  base := (8482974481201747554130306377638515431171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3186100221062041803347973369866786815000000000000)
      constant := (71814469351627007651322294715316639288747414442939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454554024086798741951/100000000000000000000)
  centralHi := (7102406626356230343/1562500000000000000)
  directionLo := (22864205141597493997/5000000000000000000)
  directionHi := (457284102831949879941/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree085.table
  base := (9326624467267728179283376638960722927217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-29008527842798928414504897660318994050000000000000)
      constant := (661792619407745962022591895968222122028488712527777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree085.table
  base := (233165607352481089143045874160602957543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-3626999031869870912664826442454111717187500000000)
      constant := (82766343997890600643756432862906079660118741418915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22864205141597493997/5000000000000000000)
  centralHi := (457284102831949879941/100000000000000000000)
  directionLo := (22999898945003030901/5000000000000000000)
  directionHi := (459997978900060618021/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree086.table
  base := (5096306980520711838616881403409299852477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-14674765145792935984688146706873556757500000000000)
      constant := (338889203506854410983479468620339829044805475169837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree086.table
  base := (5096306906918444763891110300273192592203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-14678541260179779186252731375232353070000000000000)
      constant := (339062269615273315655017618627108082618207067377243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22999898945003030901/5000000000000000000)
  centralHi := (459997978900060618021/100000000000000000000)
  directionLo := (46269593739459169243/10000000000000000000)
  directionHi := (462695937394591692431/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree087.table
  base := (5540471481893681931316253554523135370747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1649474041131823084680427175954179610000000000000)
      constant := (38553186690018367646248623830880781174437158993523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree087.table
  base := (11080942838670165806408016914500134139069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3299796976195572160410257106810724282500000000000)
      constant := (77145731755790717318323919062257485711788341145221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46269593739459169243/10000000000000000000)
  centralHi := (462695937394591692431/100000000000000000000)
  directionLo := (58172281894330269201/12500000000000000000)
  directionHi := (465378255154642153609/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree088.table
  base := (11991611305446496940766710407228836869649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-30031535189159759079119084920603352445000000000000)
      constant := (710329479539277629994250572427693305259202818651969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree088.table
  base := (2997902799779019377465499609399685404577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-7509815762790185128719791293032082736250000000000)
      constant := (177672972902449945210787967314872107017449787049937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58172281894330269201/12500000000000000000)
  centralHi := (465378255154642153609/100000000000000000000)
  directionLo := (23402260054324802197/5000000000000000000)
  directionHi := (468045201086496043941/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree089.table
  base := (12924618843146614431838202993241835568763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-30372537637946702633990480674031471910000000000000)
      constant := (726894764296337793377857909420322437772212018654603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree089.table
  base := (3231154688198334605183082616263402703333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-7595088329140332896516504095740035836875000000000)
      constant := (181816364144909885041116276101349066303674610326773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23402260054324802197/5000000000000000000)
  centralHi := (468045201086496043941/100000000000000000000)
  directionLo := (58837129559782685069/12500000000000000000)
  directionHi := (470697036478261480553/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree090.table
  base := (13879965456855535073438075740084307165437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3412615565192627354317986269717732375000000000000)
      constant := (82628134958795870017825555886038373523227661681733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree090.table
  base := (10843722953193794952202268255227223127/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-426686716416137814684067605469332718750000000000)
      constant := (10333781675687565674770170321064925388942124910880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58837129559782685069/12500000000000000000)
  centralHi := (470697036478261480553/100000000000000000000)
  directionLo := (94666803059728835489/20000000000000000000)
  directionHi := (236667007649322088723/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree091.table
  base := (14857651045729486774537879434282989088063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-31054542535520589743733272180887710840000000000000)
      constant := (760604830485371491973887242752882959390114044997903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree091.table
  base := (1485765098051280111125972382059164695923/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-15531266923681256864219859402311884076250000000000)
      constant := (380496181883599595220677803682547552175414354452815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94666803059728835489/20000000000000000000)
  centralHi := (236667007649322088723/50000000000000000000)
  directionLo := (475956384480822382799/100000000000000000000)
  directionHi := (1189890961202055957/250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree092.table
  base := (15857675525045456331004191285908806822601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-31395544984307533298604667934315830305000000000000)
      constant := (777749611820956131096247817074724241627954261020281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree092.table
  base := (15857675469648063219643463691926503346163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-31403624112763104799626570015455580555000000000000)
      constant := (778145705888872928708797128950796876088542879664003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475956384480822382799/100000000000000000000)
  centralHi := (1189890961202055957/250000000000000000)
  directionLo := (47856438419232131873/10000000000000000000)
  directionHi := (478564384192321318731/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree093.table
  base := (16880038823624083010969690766005822832749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3526283048121608539275118187527105530000000000000)
      constant := (88343062066549341654308217455909874947225814380341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree093.table
  base := (8440019388286473368971066032102357994969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1763595243231316437267412290349299608750000000000)
      constant := (44194017054315973578631682875275348995201685808321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47856438419232131873/10000000000000000000)
  centralHi := (478564384192321318731/100000000000000000000)
  directionLo := (4811582480917219237/1000000000000000000)
  directionHi := (481158248091721923701/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree094.table
  base := (8962370440832312939621763961951795729913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-16038774940940710204173729720586034617500000000000)
      constant := (406309335394136521781967918987140621378365871747753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree094.table
  base := (8962370420853388947796129823604266501427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-16042902321782143471000136218559602680000000000000)
      constant := (406516083501347503595333122866951109271262712654787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4811582480917219237/1000000000000000000)
  centralHi := (481158248091721923701/100000000000000000000)
  directionLo := (96747640714596100287/20000000000000000000)
  directionHi := (120934550893245125359/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree095.table
  base := (4747945412231523324396743819022889634597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-8104638082667090990804713798650047175000000000000)
      constant := (207585737090711593715489862517348881603190676273557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree095.table
  base := (3798356322999181696714643821490330222229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-32426894908964878013187123647951017762500000000000)
      constant := (830765285937896026512587185109382014847866592894745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96747640714596100287/20000000000000000000)
  centralHi := (120934550893245125359/25000000000000000000)
  directionLo := (486304471998082315497/100000000000000000000)
  directionHi := (243152235999041157749/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree096.table
  base := (10040580541599585203604231275647008233193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1819975265525294862116125052668239342500000000000)
      constant := (47125577294485516546139673777612994512796868177937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree096.table
  base := (1004058052719524164276664906613092679323/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-910221810399040807899277079410634171250000000000)
      constant := (23574768437818017763889093165861682473246767325535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486304471998082315497/100000000000000000000)
  centralHi := (243152235999041157749/50000000000000000000)
  directionLo := (24442863445935141103/5000000000000000000)
  directionHi := (488857268918702822061/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree097.table
  base := (21192879149022438930445092330435051609193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-33100557228242251072961646701456427630000000000000)
      constant := (866370999583532099285825863525270042075456656657433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree097.table
  base := (21192879124564788409658134102017007357919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-33109075439766060155560826069614642567500000000000)
      constant := (866811300455003621855004349432089232188029768993839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24442863445935141103/5000000000000000000)
  centralHi := (488857268918702822061/100000000000000000000)
  directionLo := (491396804287504732621/100000000000000000000)
  directionHi := (245698402143752366311/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree098.table
  base := (22326935816603823952654636274576104126379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-33441559677029194627833042454884547095000000000000)
      constant := (884674773195749891258653941758879932931587827655099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree098.table
  base := (11163467897921109498713831476054570971457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-16725082852583325613373838640223227485000000000000)
      constant := (442562098001573032091377022241704561401733269615217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491396804287504732621/100000000000000000000)
  centralHi := (245698402143752366311/50000000000000000000)
  directionLo := (61740410332457138363/12500000000000000000)
  directionHi := (98784656531931421381/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree099.table
  base := (11741665530457225840510931021866369497989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1876809006989785454594691011572925920000000000000)
      constant := (50176206229132885212167060359531365287239561823501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree099.table
  base := (4696666208658427820244595914896045357651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3754583996729693588659392054586474152500000000000)
      constant := (100403372265880694911761957615014709727051355466295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61740410332457138363/12500000000000000000)
  centralHi := (98784656531931421381/20000000000000000000)
  directionLo := (99287380677024778131/20000000000000000000)
  directionHi := (15513653230785121583/3125000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree100.table
  base := (4932412972185470260489477102065119302703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-34123564574603081737575833961740786025000000000000)
      constant := (921861816358536194225040773944638958678149808638715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree100.table
  base := (24662064845971142779053862972390280913369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-34132346235967833369121379702110079775000000000000)
      constant := (922329763613465565256813586589802876047331648305289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99287380677024778131/20000000000000000000)
  centralHi := (15513653230785121583/3125000000000000000)
  directionLo := (124734465198058364661/25000000000000000000)
  directionHi := (99787572158446691729/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree101.table
  base := (3232892149872230395978073305872538694713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-4308070877923753161555903714396113186250000000000)
      constant := (117593135736125889195206545062301233559214304976553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree101.table
  base := (6465784296571405884322671827081034938259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-8618359125342106110077057728235473044375000000000)
      constant := (235305608913906338981749095891622682138075039565379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124734465198058364661/25000000000000000000)
  centralHi := (99787572158446691729/20000000000000000000)
  directionLo := (250713172181503775749/50000000000000000000)
  directionHi := (501426344363007551499/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree102.table
  base := (27086548060226159126842293510243538828907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3867285496908552094146513940955224995000000000000)
      constant := (106646835634232941754712417150134555009578919620963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree102.table
  base := (13543274024728126705727572345375443048849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-1934140375931611972860837895765205810000000000000)
      constant := (53350464806207155811467925703648792118364978165241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250713172181503775749/50000000000000000000)
  centralHi := (501426344363007551499/100000000000000000000)
  directionLo := (503902538900697280711/100000000000000000000)
  directionHi := (62987817362587160089/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree103.table
  base := (7083074358051487970243746587665028224557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-8786642980240978100547505305506286105000000000000)
      constant := (244772780202332222529202658174391457574131388876317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree103.table
  base := (14166148711534037970313375678471047910539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-17577808516084803291340966667302758491250000000000)
      constant := (489793778087663607210483804020062879874297614308059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503902538900697280711/100000000000000000000)
  centralHi := (62987817362587160089/12500000000000000000)
  directionLo := (101273324937989083007/20000000000000000000)
  directionHi := (126591656172486353759/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree104.table
  base := (5920077060888992713803524502647182360803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-35487574369750855957061416975453263885000000000000)
      constant := (998553886187264754974653518059485321516103645969215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree104.table
  base := (14800192648346261862827653839631775991889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-17748353648785098826934392272718664692500000000000)
      constant := (499530002320501838966601815913082436658430361857409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101273324937989083007/20000000000000000000)
  centralHi := (126591656172486353759/25000000000000000000)
  directionLo := (63602347206245970987/12500000000000000000)
  directionHi := (508818777649967767897/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree105.table
  base := (30890811668146319110193591694248018693393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3980952979837533279103645858764598150000000000000)
      constant := (113134424093037190260992862946071706770185129199737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree105.table
  base := (6178162332313972131892834691538015053341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-3981977506996754302783959528474349087500000000000)
      constant := (113191745767134236467931970329127193749964646452345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63602347206245970987/12500000000000000000)
  centralHi := (508818777649967767897/100000000000000000000)
  directionLo := (102251833896224402193/20000000000000000000)
  directionHi := (255629584740561005483/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree106.table
  base := (32203576515920754006265785233681195208229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-36169579267324743066804208482309502815000000000000)
      constant := (1038058912755700558938513451649411895827709118044949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree106.table
  base := (6440715302068477607603606188591349201419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-36178887828371379796242486967100954190000000000000)
      constant := (1038584677961118758164788732936831055842138379586695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102251833896224402193/20000000000000000000)
  centralHi := (255629584740561005483/50000000000000000000)
  directionLo := (51368796780520949009/10000000000000000000)
  directionHi := (513687967805209490091/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree107.table
  base := (33538679841561635534332592247726857978863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (27970001804741645146934470260330000000000000)
      linear := (-3188975606263576436516342408571720000000000000)
      constant := (92418654374979333172158758697530099194643035447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree107.table
  base := (16769339918415149334157357752510638139621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (13985000902370822573467235130165000000000000)
      linear := (-1594898161139486892629458388415266250000000000)
      constant := (46232723504608506966307276266229865532381465149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51368796780520949009/10000000000000000000)
  centralHi := (513687967805209490091/100000000000000000000)
  directionLo := (516105336299834476853/100000000000000000000)
  directionHi := (258052668149917238427/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree108.table
  base := (6979224327971187547540670068969415916749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4094620462766514464060777776573971305000000000000)
      constant := (119815177820548932398644860663195638638551808681705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree108.table
  base := (8724030408960840217808211119250445734377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-1023918565532571164961560816354571638750000000000)
      constant := (29968955178992574190975873772919682591046139538193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516105336299834476853/100000000000000000000)
  centralHi := (258052668149917238427/50000000000000000000)
  directionLo := (518511434827125624757/100000000000000000000)
  directionHi := (259255717413562812379/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree109.table
  base := (18137950953212711990063940331313243247819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-18596293306842786865709197871296930605000000000000)
      constant := (549382596045416195589238930564465230834727527115739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree109.table
  base := (9068975475755676119620054096610024038659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-9300539656143288252450760149899097849375000000000)
      constant := (274830282216118966676408657513533928838623288537779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518511434827125624757/100000000000000000000)
  centralHi := (259255717413562812379/50000000000000000000)
  directionLo := (520906419557106097297/100000000000000000000)
  directionHi := (260453209778553048649/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree110.table
  base := (18839010318796604680432420398248625445023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-18766794531236258643144895748010990337500000000000)
      constant := (559693474527452250554501090829907403848596779927663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree110.table
  base := (18839010317353948379414285974666339009043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-18771624444986872040494945905214101900000000000000)
      constant := (559976565034426921300054840586568820545092561605283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520906419557106097297/100000000000000000000)
  centralHi := (260453209778553048649/50000000000000000000)
  directionLo := (261645221542990894987/50000000000000000000)
  directionHi := (20931617723439271599/4000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree111.table
  base := (39102477830271646958492236488373124394143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4208287945695495649017909694383344460000000000000)
      constant := (126689096808394767324882427668616912685266446306487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree111.table
  base := (19551238913912632788329429086731275492231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2104685508631907508454263501181112011250000000000)
      constant := (63376577225292780112314078652713610575365921256479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261645221542990894987/50000000000000000000)
  centralHi := (20931617723439271599/4000000000000000000)
  directionLo := (262831827274800591393/50000000000000000000)
  directionHi := (525663654549601182787/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree112.table
  base := (40549273481868130168911770256092310587329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-38215593960046404396032583002878219605000000000000)
      constant := (1161209958751430928801971591248340275974929225112049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree112.table
  base := (40549273479794073417501384872526988388403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-38225429420774926223363594232091828605000000000000)
      constant := (1161796908822383953306380109723617707272478874389443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262831827274800591393/50000000000000000000)
  centralHi := (525663654549601182787/100000000000000000000)
  directionLo := (528026199732325545151/100000000000000000000)
  directionHi := (8250409370817586643/1562500000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree113.table
  base := (42018407590205948058188873157207099822077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-38556596408833347950903978756306339070000000000000)
      constant := (1182411211481407921477048563131530871938391612867437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree113.table
  base := (42018407588447688892419972619643052419601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-38566519686175517294550445442923641007500000000000)
      constant := (1183008686369070163803090056488391224626710875577281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528026199732325545151/100000000000000000000)
  centralHi := (8250409370817586643/1562500000000000000)
  directionLo := (530378221171534390659/100000000000000000000)
  directionHi := (26518911058576719533/5000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree114.table
  base := (10877470038364447059380966909726492439157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-1080488857156119208493760403048179403750000000000)
      constant := (33439045262903742323832533338415673676518914713213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree114.table
  base := (5438735018995919810970345374205285392363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-540383471549668171746351342413270186250000000000)
      constant := (16727968370755332763255131139977789522580938658467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530378221171534390659/100000000000000000000)
  centralHi := (26518911058576719533/5000000000000000000)
  directionLo := (532719858257978170033/100000000000000000000)
  directionHi := (266359929128989085017/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree115.table
  base := (45023691170089866208208573261640448520151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-39238601306407235060646770263162578000000000000000)
      constant := (1225393212700014642151852767324835314695893956001831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree115.table
  base := (2251184558441328227281330864587119021347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-9812175054244174859231036966146816453125000000000)
      constant := (306503004449383105045033193007090401576594334501535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532719858257978170033/100000000000000000000)
  centralHi := (266359929128989085017/50000000000000000000)
  directionLo := (267525623666089064599/50000000000000000000)
  directionHi := (535051247332178129199/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree116.table
  base := (46559840638814983114313759247661113260207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-39579603755194178615518166016590697465000000000000)
      constant := (1247173961187179067667574379255682294351854192003967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree116.table
  base := (9311968127548855481629050028136393150279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-39589790482377290508110999075419078215000000000000)
      constant := (1247803571677850142653843022586185382887700030154995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267525623666089064599/50000000000000000000)
  centralHi := (535051247332178129199/100000000000000000000)
  directionLo := (537372521777061982807/100000000000000000000)
  directionHi := (67171565222132747851/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree117.table
  base := (1924733142342123408195455083710514784023/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4435622911553458018932173530002090770000000000000)
      constant := (141016430547274109803312848949443156888016252185175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree117.table
  base := (24059164278822840067005200784012021666359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2218382263765437865516547238125049478750000000000)
      constant := (70543799129709935253030169363984675436634729866831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537372521777061982807/100000000000000000000)
  centralHi := (67171565222132747851/12500000000000000000)
  directionLo := (21587352484280540187/4000000000000000000)
  directionHi := (134920953026753376169/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree118.table
  base := (24849577464199063149565740822920774975669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-20130804326384032862630478761723468197500000000000)
      constant := (645657476957203888279957482253251566523884531431589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree118.table
  base := (12424788731907292857392568006238404358893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-10067992753294618162621175374270675755000000000000)
      constant := (322991613941962544352470527090065253514682550503133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21587352484280540187/4000000000000000000)
  centralHi := (134920953026753376169/25000000000000000000)
  directionLo := (108397049210700852477/20000000000000000000)
  directionHi := (270992623026752131193/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree119.table
  base := (6412789968448778262630464985580164784983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5075326387694376160016544159609381982500000000000)
      constant := (164209399769200841034765013130697965338488028280423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree119.table
  base := (51302319746938643343881341701389554063961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-40613061278579063721671552707914515422500000000000)
      constant := (1314337785976671426308100045867828327469956765826441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108397049210700852477/20000000000000000000)
  centralHi := (270992623026752131193/50000000000000000000)
  directionLo := (544276948647466475597/100000000000000000000)
  directionHi := (272138474323733237799/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree120.table
  base := (52927823015492278149136389042049273755699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4549290394482439203889305447811463925000000000000)
      constant := (148469845293636990153153109484240767733689378166891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree120.table
  base := (52927823014940190665730833497550137850409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4550461282664406088095378213194036425000000000000)
      constant := (148544708328990368007505818960262486278904885843281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544276948647466475597/100000000000000000000)
  centralHi := (272138474323733237799/50000000000000000000)
  directionLo := (109311808459711462281/20000000000000000000)
  directionHi := (273279521149278655703/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree121.table
  base := (3410979045723143525363560080029114252221/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5160576999891112048734393097966411848750000000000)
      constant := (169871897797688619707940433087698089969346790143002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree121.table
  base := (6821958091387817963802295298885647392187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5161905226172530733005656891197267528437500000000)
      constant := (169957527840037484680673773888890828036906081552347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109311808459711462281/20000000000000000000)
  centralHi := (273279521149278655703/50000000000000000000)
  directionLo := (137207911717864201127/25000000000000000000)
  directionHi := (548831646871456804509/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree122.table
  base := (7030730611922112887587485241519806258681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5203202305989479993093317567144926781875000000000)
      constant := (172739365296212810730124835395971097945753475310761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree122.table
  base := (56245844894980629394146056987170775503211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-41636332074780836935232106340409952630000000000000)
      constant := (1382611329254599938271674692667028666139030504205691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137207911717864201127/25000000000000000000)
  centralHi := (548831646871456804509/100000000000000000000)
  directionLo := (34443429984958372941/6250000000000000000)
  directionHi := (551094879759333967057/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree123.table
  base := (11587672701307491179317277996650590586549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4662957877411420388846437365620837080000000000000)
      constant := (156116425289679877284567043765520799505393194422705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree123.table
  base := (57938363506201760607854062147580444996533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4664158037797936445157661950137973892500000000000)
      constant := (156195077173735545533359344727301478846213159143997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34443429984958372941/6250000000000000000)
  centralHi := (551094879759333967057/100000000000000000000)
  directionLo := (553348855954608497737/100000000000000000000)
  directionHi := (276674427977304248869/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree124.table
  base := (59653220564738392647678058061772594130911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-42307623345489727054489332044015653185000000000000)
      constant := (1428373898093595313338471844247212408008961572969391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree124.table
  base := (59653220564454033813228130299026181036871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-42318512605582019077605808762073577435000000000000)
      constant := (1429093318647197780075659079852432541346630152768151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553348855954608497737/100000000000000000000)
  centralHi := (276674427977304248869/50000000000000000000)
  directionLo := (555593688117128779931/100000000000000000000)
  directionHi := (138898422029282194983/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree125.table
  base := (61390416069717439404667277181028103917333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-42648625794276670609360727797443772650000000000000)
      constant := (1451893133828995506299280572733515680316690130560773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree125.table
  base := (61390416069476581921790506035212197329933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-42659602870982610148792659972905389837500000000000)
      constant := (1452624201505198046989398225320898115664677399941373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555593688117128779931/100000000000000000000)
  centralHi := (138898422029282194983/25000000000000000000)
  directionLo := (557829486639880544577/100000000000000000000)
  directionHi := (278914743319940272289/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree126.table
  base := (6314995002125538393881712768384505349203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2388312680170200786901784641715105117500000000000)
      constant := (81978085267400311616971414563230459419932948830135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree126.table
  base := (63149950021051385925259925201625255334703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-4777854792931466802219945687081911360000000000000)
      constant := (164038704793056384999725340617006054040491480835527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557829486639880544577/100000000000000000000)
  centralHi := (278914743319940272289/50000000000000000000)
  directionLo := (280028179856167318691/50000000000000000000)
  directionHi := (560056359712334637383/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree127.table
  base := (64931822419169164627776504929515199907149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-43330630691850557719103519304300011580000000000000)
      constant := (1499511101046130534116985335707589473486796634689469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree127.table
  base := (64931822418996396137077841555162211681683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-43341783401783792291166362394569014642500000000000)
      constant := (1500265743544031472089433344886022839235352324233123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280028179856167318691/50000000000000000000)
  centralHi := (560056359712334637383/100000000000000000000)
  directionLo := (70284301672692093329/12500000000000000000)
  directionHi := (562274413381536746633/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree128.table
  base := (66736033263306064515405395962193151884473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-43671633140637501273974915057728131045000000000000)
      constant := (1523609832527690955613969095520848653423736359243113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree128.table
  base := (16684008315789938430562326904180951536197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-10920718416796095840588303401350206761250000000000)
      constant := (381094100681172797069723901528530722842723267663157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70284301672692093329/12500000000000000000)
  centralHi := (562274413381536746633/100000000000000000000)
  directionLo := (112896750322207338721/20000000000000000000)
  directionHi := (282241875805518346803/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree129.table
  base := (34281291276769416970485829985981218785623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2445146421634691379380350600619791695000000000000)
      constant := (85994540514323376463653071525032434153249429141807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree129.table
  base := (6856258255341493664615277505187380484329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2445775774032498579641114712012924413750000000000)
      constant := (86037795593301160792546217079459574916196534982805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112896750322207338721/20000000000000000000)
  centralHi := (282241875805518346803/50000000000000000000)
  directionLo := (56668447633774994059/10000000000000000000)
  directionHi := (566684476337749940591/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree130.table
  base := (35205735144880796675127909389991737689067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-22176819019105694191858853282292184987500000000000)
      constant := (786193395618232499664635632871186926337967748997627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree130.table
  base := (2200358446551771321246834294733865876343/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5545631774748195688090864503383056481250000000000)
      constant := (196647187176020739189562116293569288109041894746332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56668447633774994059/10000000000000000000)
  centralHi := (566684476337749940591/100000000000000000000)
  directionLo := (284438343763419655821/50000000000000000000)
  directionHi := (568876687526839311643/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree131.table
  base := (72282696471886391609797225722711758560967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-44694640486998331938589102318012489440000000000000)
      constant := (1597065018463577940135319978273720129708647107861527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree131.table
  base := (72282696471797562514725508312600799144019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-44706144463386156575913767237896264252500000000000)
      constant := (1597867932910880833276246221106445526231754112227939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284438343763419655821/50000000000000000000)
  centralHi := (568876687526839311643/100000000000000000000)
  directionLo := (57106048322470052961/10000000000000000000)
  directionHi := (571060483224700529611/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree132.table
  base := (1159004079685004922908418223539692162097/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-625495040774795492964729139881119568125000000000)
      constant := (22526894596376690628446467382167054043793884445384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree132.table
  base := (74176261099765107078772419606034674018019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5005248303198527516344513160969786295000000000000)
      constant := (180305736354169778926098349696707693489457621935771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106048322470052961/10000000000000000000)
  centralHi := (571060483224700529611/100000000000000000000)
  directionLo := (286617979805065516203/50000000000000000000)
  directionHi := (573235959610131032407/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree133.table
  base := (76092164173563059329757603274445396689509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-45376645384572219048331893824868728370000000000000)
      constant := (1647000968663065030777935538370666402481225115916629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree133.table
  base := (76092164173499387419556576330407801268949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-45388324994187338718287469659559889057500000000000)
      constant := (1647828580238076316023514747719379258318822824275269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286617979805065516203/50000000000000000000)
  centralHi := (573235959610131032407/100000000000000000000)
  directionLo := (287701605521878812847/50000000000000000000)
  directionHi := (115080642208751525139/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree134.table
  base := (39015202846502444913480581574090996223379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-22858823916679581301601644789148423917500000000000)
      constant := (836129345817691011555470917201880885593281958712099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree134.table
  base := (78030405692950987521385958739123349713037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-45729415259587929789474320870391701460000000000000)
      constant := (1673098792062500082196867825642255084115469250451197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287701605521878812847/50000000000000000000)
  centralHi := (115080642208751525139/20000000000000000000)
  directionLo := (577562330115794843289/100000000000000000000)
  directionHi := (57756233011579484329/10000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree135.table
  base := (79990985658124928979669464813292965636493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5117627809127345128674965036858329700000000000000)
      constant := (188634397761783496579980266936949501214942502327637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree135.table
  base := (2499718301814978118579212233274631886807/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-639868132291507234175849612239215470312500000000)
      constant := (23591142536955253000938429759200473105474889858252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577562330115794843289/100000000000000000000)
  centralHi := (57756233011579484329/10000000000000000000)
  directionLo := (579713407692202406537/100000000000000000000)
  directionHi := (289856703846101203269/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree136.table
  base := (81973904068889717801707886117661455761851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-46399652730933049712946081085153086765000000000000)
      constant := (1723353633325055989514061975062248027402373876899531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree136.table
  base := (16394780813770218812003433279609490111043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-46411595790389111931848023292055326265000000000000)
      constant := (1724218992032893456894341875627178635359758600336415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579713407692202406537/100000000000000000000)
  centralHi := (289856703846101203269/50000000000000000000)
  directionLo := (581856532959306886967/100000000000000000000)
  directionHi := (72732066619913360871/12500000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree137.table
  base := (20994790231318002010660787419074933470653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-11685163794929998316954369209645301557500000000000)
      constant := (437297713010595357610907546727250157589476260651693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree137.table
  base := (41989580462619657980382085794840631839331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-23376343027894851501517437251443569333750000000000)
      constant := (875034490089415875920565329753844241335657769583411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581856532959306886967/100000000000000000000)
  centralHi := (72732066619913360871/12500000000000000000)
  directionLo := (29199589673347478523/5000000000000000000)
  directionHi := (583991793466949570461/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree138.table
  base := (1075084452840621850246945289890113100983/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-653911911507040789204012119333462856875000000000)
      constant := (24655850500111338023750089807719674043788911640470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree138.table
  base := (86006756227222078109451489186238167266809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5232641813465588230469080634857661230000000000000)
      constant := (197345803010953525772146388937533632448922026750881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29199589673347478523/5000000000000000000)
  centralHi := (583991793466949570461/100000000000000000000)
  directionLo := (586119275170219584837/100000000000000000000)
  directionHi := (293059637585109792419/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree139.table
  base := (44028344987402615584201282621910843535613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-23711330038646940188780134172718722580000000000000)
      constant := (900722392610975756998983413874341808020331872729453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree139.table
  base := (4402834498739090657364611975417516960967/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-11858716646647721286352144231137690868125000000000)
      constant := (450587183198033568052832929239670463337868703807635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586119275170219584837/100000000000000000000)
  centralHi := (293059637585109792419/50000000000000000000)
  directionLo := (588239062469828575797/100000000000000000000)
  directionHi := (294119531234914287899/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree140.table
  base := (2253224054198109532242855774106157831457/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-5970457815760102991553958012358195578125000000000)
      constant := (228482687460522455964002833443660355128271806376085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree140.table
  base := (90128962167904562815051204052790445724671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-47775956851991476216595428135382575875000000000000)
      constant := (1828778497259482122293031444219229295132613671359951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588239062469828575797/100000000000000000000)
  centralHi := (294119531234914287899/50000000000000000000)
  directionLo := (36896952390698786791/6250000000000000000)
  directionHi := (590351238251180588657/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree141.table
  base := (23055893201649038158153568544131690608147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-1336240693746326874647307218119269002500000000000)
      constant := (51513093872074861148922666490466436829588804690123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree141.table
  base := (92223572806579381277111695613824211657671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5346338568599118587531364371801598697500000000000)
      constant := (206155724500068844066946003105099297942744642081439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36896952390698786791/6250000000000000000)
  centralHi := (590351238251180588657/100000000000000000000)
  directionLo := (296227941961094163233/50000000000000000000)
  directionHi := (592455883922188326467/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree142.table
  base := (9434052189081202644088420270712342245911/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 515205000000000000000000000000000000000000000
      center := (9067608)
      previous := (4533804)
      next := (4533804)
      square := (31762403358707309590086565166685000000000000)
      linear := (-4805164394331949121421786907927177500000000000)
      constant := (186597344212804319584479440380401467286804576755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree142.table
  base := (2948141309087432325545671543021042734373/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 128801250000000000000000000000000000000000000
      center := (2266902)
      previous := (1133451)
      next := (1133451)
      square := (7940600839676827397521641291671250000000000)
      linear := (-1201600312011323605409867351642685000000000000)
      constant := (46672728687649829255345906596187126854445113172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296227941961094163233/50000000000000000000)
  centralHi := (592455883922188326467/100000000000000000000)
  directionLo := (118910615889976920039/20000000000000000000)
  directionHi := (148638269862471150049/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree143.table
  base := (24119952355141397132883368502034678239963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-12196667468110413649261462839787480755000000000000)
      constant := (477067658640142690515878796795714768897715372541803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree143.table
  base := (96479809420553579748676944479206755663519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-48799227648193249430155981767878013082500000000000)
      constant := (1909227343304246980638039315729776253870627867507439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118910615889976920039/20000000000000000000)
  centralHi := (148638269862471150049/25000000000000000000)
  directionLo := (298321451697937777977/50000000000000000000)
  directionHi := (119328580679175111191/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree144.table
  base := (98641435395852174937269749296336562906447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5458630257914288683546360790286449165000000000000)
      constant := (215051112223991712755172616387980659173236910894823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree144.table
  base := (770636214030015734610917788102023971691/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-682504415466581118074206013593192020625000000000)
      constant := (26894863095371266733723428625983065639929660729904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298321451697937777977/50000000000000000000)
  centralHi := (119328580679175111191/20000000000000000000)
  directionLo := (598725432950680150373/100000000000000000000)
  directionHi := (299362716475340075187/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree145.table
  base := (100825399816668574718317750472751437159589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-49468674770015541706788642866006161950000000000000)
      constant := (1962842550719555440392413615927476209742971860361109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree145.table
  base := (100825399816659977755023986891858608585953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-49481408178994431572529684189541637887500000000000)
      constant := (1963826201202993345638019697620824055199436677870993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598725432950680150373/100000000000000000000)
  centralHi := (299362716475340075187/50000000000000000000)
  directionLo := (600800743966998341209/100000000000000000000)
  directionHi := (60080074396699834121/10000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree146.table
  base := (103031702683012780790168742034580559209671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-49809677218802485261660038619434281415000000000000)
      constant := (1990418256671459796311829279965875686334081019644951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree146.table
  base := (6439481417687844212321669308776307721791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-6227812305549377830464566925046681286250000000000)
      constant := (248926939789129047894268617205018495248934846757342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600800743966998341209/100000000000000000000)
  centralHi := (60080074396699834121/10000000000000000000)
  directionLo := (301434455495974279899/50000000000000000000)
  directionHi := (602868910991948559799/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree147.table
  base := (105260343994883781076956013101994813805921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5572297740843269868503492708095822320000000000000)
      constant := (224243014207959772983617327352910610629248771215689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree147.table
  base := (52630171997438813884096070381429180890579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2786866039433089650827965922844736816250000000000)
      constant := (112177671899824878379704934330058123585844485652811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301434455495974279899/50000000000000000000)
  centralHi := (602868910991948559799/100000000000000000000)
  directionLo := (151232501824578307221/25000000000000000000)
  directionHi := (120986001459662645777/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree148.table
  base := (26877830938070345882373382272776333260087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-12622920529094093092850707531572630086250000000000)
      constant := (511537291080022455564636544076217818833386680442247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree148.table
  base := (26877830938069044513809592918173929825241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-12626169743799051196522559455509268773750000000000)
      constant := (511793482213609886287158652444433134160391318378121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151232501824578307221/25000000000000000000)
  centralHi := (120986001459662645777/20000000000000000000)
  directionLo := (121396820982965875637/20000000000000000000)
  directionHi := (303492052457414689093/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree149.table
  base := (27446160488801517394983162989315493046463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-12708171141290828981568556469929659952500000000000)
      constant := (518576091504203910649987193859021484228200744268303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree149.table
  base := (54892320977600833069836528948369616429949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-25422884620298397928638544516434443748750000000000)
      constant := (1037671511142903924952326744630717262742691392916269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121396820982965875637/20000000000000000000)
  centralHi := (303492052457414689093/50000000000000000000)
  directionLo := (152257818663889946357/25000000000000000000)
  directionHi := (609031274655559785429/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree150.table
  base := (3502509331364339733527073635030301697349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-710745652971531381682578078238149434375000000000)
      constant := (29203510180025221584100602588219575675716777606964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree150.table
  base := (22416059720731029332121063667062144774379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-5687428833999709658718215582633411100000000000000)
      constant := (233745041610105919212622386238526380619003611635055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152257818663889946357/25000000000000000000)
  centralHi := (609031274655559785429/100000000000000000000)
  directionLo := (76383948268547315947/12500000000000000000)
  directionHi := (611071586148378527577/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree151.table
  base := (57199146848820634820954593735796126098889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-25757344731368601518008508693287439370000000000000)
      constant := (1065597132577545762802795076994328069837769187724409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree151.table
  base := (114398293697638119011945532625958719835733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-51527949771397977999650791454532512302500000000000)
      constant := (2132260985469876593005179132271361964159224414591173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76383948268547315947/12500000000000000000)
  centralHi := (611071586148378527577/100000000000000000000)
  directionLo := (613105107862603361059/100000000000000000000)
  directionHi := (30655255393130168053/5000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree152.table
  base := (116738627237155106913459393345777543481151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-51855691911524146590888413140002998205000000000000)
      constant := (2159928962596643314469717258651317873337377893442831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree152.table
  base := (58369313618576221035946852851992335567769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-25934520018399284535418821332682162352500000000000)
      constant := (1080504927611289387867948452026525099630911205551689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613105107862603361059/100000000000000000000)
  centralHi := (30655255393130168053/5000000000000000000)
  directionLo := (615131907135805956513/100000000000000000000)
  directionHi := (307565953567902978257/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree153.table
  base := (14887662402775314604265357838253287633573/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4447618759201209656767399305701641250000000000)
      linear := (-724954088337654029802219567964321078750000000000)
      constant := (30400789240089894845486911052394748762063049253357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree153.table
  base := (59550649611100131487880567311228564050961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2900562794566620007890249659788674283750000000000)
      constant := (121663999097170052021753589019765209336010484997049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615131907135805956513/100000000000000000000)
  centralHi := (307565953567902978257/50000000000000000000)
  directionLo := (308576025099914844461/50000000000000000000)
  directionHi := (617152050199829688923/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree154.table
  base := (121486309652785863850788389013428848437909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-52537696809098033700631204646859237135000000000000)
      constant := (2217977853224580096985504352781937284905300420177029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree154.table
  base := (15185788706597994709170423894970777982011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-6568902570949968901651418135878493688750000000000)
      constant := (277385921381165538638879625204651807507377172468491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308576025099914844461/50000000000000000000)
  centralHi := (617152050199829688923/100000000000000000000)
  directionLo := (123833120441208684857/20000000000000000000)
  directionHi := (309582801103021712143/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree155.table
  base := (15486707316113461679466647300490542844111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-6609837407235622156937825050035919575000000000000)
      constant := (280911505801370955124363809150828264311080284458591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree155.table
  base := (123893658528906081373748605619267608803797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-52892310833000342284398196297859761912500000000000)
      constant := (2248416017123370221145734860534490734014120317298757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123833120441208684857/20000000000000000000)
  centralHi := (309582801103021712143/50000000000000000000)
  directionLo := (12423452544997170907/2000000000000000000)
  directionHi := (621172627249858545351/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree156.table
  base := (63161672925285345277224805692055429882319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-2956650094815106711687444230761970892500000000000)
      constant := (126488855824757580864113620014497847583398980634471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree156.table
  base := (31580836462642331820939122124936947176067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8895237518402419313534798611403282500000000000)
      linear := (-1478705586066692593210695764130321508750000000000)
      constant := (63276053388088890872978549913614433763530925849403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12423452544997170907/2000000000000000000)
  centralHi := (621172627249858545351/100000000000000000000)
  directionLo := (12463463767890706367/2000000000000000000)
  directionHi := (623173188394535318351/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree157.table
  base := (32193842904444411282599505415986305981087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-13390176038864716091311347976785898882500000000000)
      constant := (576624982132146997457990357375014782697843162443247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree157.table
  base := (128775371617776492302076631053387376848837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-53574491363801524426771898719523386717500000000000)
      constant := (2307653085592815312747709934406241670994299438130997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12463463767890706367/2000000000000000000)
  centralHi := (623173188394535318351/100000000000000000000)
  directionLo := (625167347694303616787/100000000000000000000)
  directionHi := (156291836923575904197/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree158.table
  base := (65624867915265711688201138155642763614001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-26950853302122903960058393830285857497500000000000)
      constant := (1168196808729911866312336030152081835718978946563681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree158.table
  base := (65624867915265224272424823928407344496653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-26957790814601057748979374965177599560000000000000)
      constant := (1168780753994108718484775993731769448322141073357693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625167347694303616787/100000000000000000000)
  centralHi := (156291836923575904197/25000000000000000000)
  directionLo := (313577583108410992109/50000000000000000000)
  directionHi := (627155166216821984219/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree159.table
  base := (133746438488834944043466277725072534589201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-6026967672559194608332020379333314940000000000000)
      constant := (262942274626593911113119992014012423855322793497209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree159.table
  base := (66873219244417059879475929708839915116691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-3014259549700150364952533396732611751250000000000)
      constant := (131536843842078220154092291553875208032585612100619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313577583108410992109/50000000000000000000)
  centralHi := (627155166216821984219/100000000000000000000)
  directionLo := (314568352032499016457/50000000000000000000)
  directionHi := (125827340812999606583/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree160.table
  base := (3406636989817278969747615960982279289053/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-6822963937727461878732447395928494240625000000000)
      constant := (299595061383394240648890226644008744013828532910465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree160.table
  base := (68132739796345230915200873137429125016617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-27298881080001648820166226176009411962500000000000)
      constant := (1198979064550194212767484683815649498817490488009177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314568352032499016457/50000000000000000000)
  centralHi := (125827340812999606583/20000000000000000000)
  directionLo := (631112020398192236593/100000000000000000000)
  directionHi := (315556010199096118297/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree161.table
  base := (3470171478552575900036870102838507926601/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-6865589243825829823091371865107009173750000000000)
      constant := (303404209467906431251433098790547295492511019221405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree161.table
  base := (34701714785525611680606800918853342453231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80057137665621773821813187502629542500000000000)
      linear := (-13734713106350972177879825890712659081875000000000)
      constant := (607111581954290092244846938951664556241148348249311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631112020398192236593/100000000000000000000)
  centralHi := (315556010199096118297/50000000000000000000)
  directionLo := (316540586726413140333/50000000000000000000)
  directionHi := (633081173452826280667/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree162.table
  base := (70685288568536773750278511243366063599923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-3070317577744087896644576148571344047500000000000)
      constant := (136550001425979962118436656688153397928825968390507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree162.table
  base := (141370577137073049284504020479586781562421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-6142215854533831086967350530409160970000000000000)
      constant := (273236420589747259814670071613414452253962224624189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316540586726413140333/50000000000000000000)
  centralHi := (633081173452826280667/100000000000000000000)
  directionLo := (127008844112483256061/20000000000000000000)
  directionHi := (317522110281208140153/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree163.table
  base := (71978316788802828836309062303348110967307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-27803359424090262847236883213856156160000000000000)
      constant := (1244379770420159534671052150213236691843888376439067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree163.table
  base := (143956633577605236463367329563946940988169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-55621032956205070853893005984514261132500000000000)
      constant := (2490002501572084874713094207835083098920441698444089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127008844112483256061/20000000000000000000)
  centralHi := (317522110281208140153/50000000000000000000)
  directionLo := (637001218177050362959/100000000000000000000)
  directionHi := (7962515227213129537/1250000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree164.table
  base := (73282514231851157306979387729524556946783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-27973860648483734624672581090570215892500000000000)
      constant := (1259906110630646117485459621068540840794033827666223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree164.table
  base := (146565028463701958522339114690706931575527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-55962123221605661925079857195346073535000000000000)
      constant := (2521070476610240510576914649775610832677764817016887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637001218177050362959/100000000000000000000)
  centralHi := (7962515227213129537/1250000000000000000)
  directionLo := (319476110941164667809/50000000000000000000)
  directionHi := (638952221882329335619/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree165.table
  base := (74597880897683221484193502602952715118997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-3127151319208578489123142107476030625000000000000)
      constant := (141725448162808907453616938291718424193975776527773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree165.table
  base := (149195761795366141938600019254278639853357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-6255912609667361444029634267353098437500000000000)
      constant := (283592412269132640669177818413338599439991595921013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319476110941164667809/50000000000000000000)
  centralHi := (638952221882329335619/100000000000000000000)
  directionLo := (16022432160444710407/2500000000000000000)
  directionHi := (640897286417788416281/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree166.table
  base := (75924416786300469086960240152091233883937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-28314863097270678179543976843998335357500000000000)
      constant := (1291248538924062435450553556764052098559229786934097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree166.table
  base := (75924416786300341850594965855847608410527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160114275331243547643626375005259085000000000000)
      linear := (-28322151876203422033726779808504849170000000000000)
      constant := (1291893101503973072916122102712952548798480456651887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16022432160444710407/2500000000000000000)
  centralHi := (640897286417788416281/100000000000000000000)
  directionLo := (642836465694817301831/100000000000000000000)
  directionHi := (80354558211852162729/12500000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree167.table
  base := (154524243795408661885523675660586393480387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-56970728643328299913959349441424790180000000000000)
      constant := (2614129254013987331607451244235722255552832899166547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree167.table
  base := (154524243795408446777168379930136453657431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-56985394017807435138640410827841510742500000000000)
      constant := (2615433954367499137115912612961243749890531917609511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642836465694817301831/100000000000000000000)
  centralHi := (80354558211852162729/12500000000000000000)
  directionLo := (32238490640704758461/5000000000000000000)
  directionHi := (644769812814095169221/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree168.table
  base := (31444398492758487675520278065354640470273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35580950073609677254139194445613130000000000000)
      linear := (-6367970121346138163203416132761434405000000000000)
      constant := (293994955047572131477343380290006287420746441318285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree168.table
  base := (78610996231896128275431568178151868152677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17790475036804838627069597222806565000000000000)
      linear := (-3184804682400445900545959002148517952500000000000)
      constant := (147070831361158567081226981420416335680177674822893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell208.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32238490640704758461/5000000000000000000)
  centralHi := (644769812814095169221/100000000000000000000)
  directionLo := (323348690041278280889/50000000000000000000)
  directionHi := (646697380082556561779/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 48539
  qDenominator := 91164
  table := BinomialMassData.Q48539_91164.Degree169.table
  base := (399855198944387629404114861354547409887/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40028568832810886910906593751314771250000000000)
      linear := (-7206591692612773377962767618535128638750000000000)
      constant := (334746637761326484014646121623355039671708407802350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q48539_91164.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree169.table
  base := (6397683183110195922905067189490729568887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320228550662487095287252750010518170000000000000)
      linear := (-57667574548608617281014113249505135547500000000000)
      constant := (2679309233408012803508579520217806434487637298376175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell208.Kernel169
