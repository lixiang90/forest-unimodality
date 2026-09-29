import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell347.Parameters
import ForestUnimodality.BinomialMassData.Q107_156.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_156.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_156.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_13.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_13.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_13.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree000.table
  base := (978334673722463638161350729/125000000000000000000000000)
  polynomial :=
    { denominator := 62400000000000000000000000000000000000000
      center := (107)
      previous := (0)
      next := (49)
      square := (599123861333594048828032893600000000000)
      linear := (-1016831016429655348831673212800000000000)
      constant := (488384669122253848170146283916800000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree000.table
  base := (978334673722463638161350729/125000000000000000000000000)
  polynomial :=
    { denominator := 5200000000000000000000000000000000000000
      center := (9)
      previous := (0)
      next := (4)
      square := (49926988444466170735669407800000000000)
      linear := (-84735918035804612402639434400000000000)
      constant := (40698722426854487347512190326400000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree001.table
  base := (62151265687393409701430833981062294953977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-1792738405552596005418375377670000000000000)
      constant := (379083120651021862209552086483526752499996068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree001.table
  base := (62001824081528197271089145211703320595003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-50006318161646275861909049690000000000000)
      constant := (10505150939920940145507715609732861180555507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29382451032349908141/100000000000000000000)
  directionHi := (14691225516174954071/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree002.table
  base := (49292298201629364543705461315514486357659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-2594066570086278045725869372860000000000000)
      constant := (302353611609919820199029233892445134999997356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree002.table
  base := (9810928793798401579436136379820270710059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-14494692592331210538592056640000000000000)
      constant := (1671894869642847297163389554257625749999971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29382451032349908141/100000000000000000000)
  centralHi := (14691225516174954071/50000000000000000000)
  directionLo := (1662122429828503513/4000000000000000000)
  directionHi := (20776530372856293913/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree003.table
  base := (19511543914325518026563219720033646614333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-1131798244873320028677787789350000000000000)
      constant := (80643271258790709844818733890567720667734648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree003.table
  base := (19369789290902907117201042879281966582429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-94940607761665829524011516710000000000000)
      constant := (6674179322260919639113239877352304704861002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1662122429828503513/4000000000000000000)
  centralHi := (20776530372856293913/50000000000000000000)
  directionLo := (12722974509733662681/25000000000000000000)
  directionHi := (2035675921557386029/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree004.table
  base := (15406742522618860808093915773960560317849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-4196722899153642126340857363240000000000000)
      constant := (194586297451104035515262870288732097947586632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree004.table
  base := (30512787577432822826670315155651054640289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-117407752561675606355062750220000000000000)
      constant := (5357356844172271511318557891705028234208841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/25000000000000000000)
  centralHi := (2035675921557386029/4000000000000000000)
  directionLo := (58764902064699816283/100000000000000000000)
  directionHi := (14691225516174954071/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree005.table
  base := (606076311376252094417944107298385993943/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-999610212737464833329670271686000000000000)
      constant := (31553024302957401811619912459905793097193696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree005.table
  base := (4788797639275479013323719104088313399883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-27974979472337076637222796746000000000000)
      constant := (867257825518705835557583382405924964580227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58764902064699816283/100000000000000000000)
  centralHi := (14691225516174954071/25000000000000000000)
  directionLo := (8212644731736658367/12500000000000000000)
  directionHi := (65701157853893266937/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree006.table
  base := (4751254147643030081276413360081733667291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-1933126409407002068985281784540000000000000)
      constant := (43199958730351230906565161079308023509064592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree006.table
  base := (467985064560240238307989548029588037269/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-32468408432339032003433043448000000000000)
      constant := (711589542964367183643119128972003026387688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/12500000000000000000)
  centralHi := (65701157853893266937/100000000000000000000)
  directionLo := (17993003105392525567/25000000000000000000)
  directionHi := (71972012421570102269/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree007.table
  base := (14807374281334276015625071916838767515341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-6600707392754688247263339348810000000000000)
      constant := (108314014190767312385051050771970811563334644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree007.table
  base := (908881914661513502683132489427213742551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-184809186961704936848216450750000000000000)
      constant := (2972153108797444452039100975126185959857904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/25000000000000000000)
  centralHi := (71972012421570102269/100000000000000000000)
  directionLo := (77738658341130902739/100000000000000000000)
  directionHi := (3886932917056545137/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree008.table
  base := (11438535976777265170991013212894062682451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-7402035557288370287570833344000000000000000)
      constant := (92620224688325173993564285303487477360031884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree008.table
  base := (279928248450408822572526027969895962359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-41455266352342942735853536852000000000000)
      constant := (508514656280962630542124697751299341109368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77738658341130902739/100000000000000000000)
  centralHi := (3886932917056545137/5000000000000000000)
  directionLo := (83106121491425175651/100000000000000000000)
  directionHi := (20776530372856293913/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree009.table
  base := (1746005349085378449074678564486795997217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4056000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (38943050986683613173822138084000000000000)
      linear := (-546890914788136821858555155946000000000000)
      constant := (5432900413375884789626996846507472282356076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree009.table
  base := (8513697085349630599874904424652043366169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-229743476561724490510318917770000000000000)
      constant := (2240349216800712192641755595841195328882561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83106121491425175651/100000000000000000000)
  centralHi := (20776530372856293913/25000000000000000000)
  directionLo := (3525894123881988977/4000000000000000000)
  directionHi := (44073676548524862213/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree010.table
  base := (6547744974897588149744853093977194719681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-9004691886355734368185821334380000000000000)
      constant := (74117984517952803599930609002732252674539204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree010.table
  base := (6356215068261227994870023148056923746107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-252210621361734267341370151280000000000000)
      constant := (2042565020578584799344592260921620113092083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3525894123881988977/4000000000000000000)
  centralHi := (44073676548524862213/50000000000000000000)
  directionLo := (92915468500591449297/100000000000000000000)
  directionHi := (46457734250295724649/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree011.table
  base := (598119412794379196924624905246422349557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-9806020050889416408493315329570000000000000)
      constant := (69844281692784770585959380343547618597638304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree011.table
  base := (4617016396387532607315905854906853643481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-274677766161744044172421384790000000000000)
      constant := (1931024886866980463602720431634258265748289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92915468500591449297/100000000000000000000)
  centralHi := (46457734250295724649/50000000000000000000)
  directionLo := (97450565495295315961/100000000000000000000)
  directionHi := (48725282747647657981/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree012.table
  base := (1678349551757253058718705831009532451003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-3535782738474366149600269774920000000000000)
      constant := (22718503151661973897041928615634663621268168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree012.table
  base := (1605302439759799662940636886986573865831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-297144910961753821003472618300000000000000)
      constant := (1891279959520587461601153995641461966650878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97450565495295315961/100000000000000000000)
  centralHi := (48725282747647657981/50000000000000000000)
  directionLo := (12722974509733662681/12500000000000000000)
  directionHi := (101783796077869301449/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree013.table
  base := (548835919875006930141886251728598949181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (8025)
      previous := (0)
      next := (3675)
      square := (44934289600019553662102467020000000000000)
      linear := (-877590490765906191469869486150000000000000)
      constant := (5280014651122677417461036586184687232866832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree013.table
  base := (1034540884602707251493227561323342933787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-24585542750904892141117219370000000000000)
      constant := (147065796157770422069148340129406916278462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/12500000000000000000)
  centralHi := (101783796077869301449/100000000000000000000)
  directionLo := (105939933795947420231/100000000000000000000)
  directionHi := (13242491724493427529/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree014.table
  base := (3897002315590624992373142785343942431/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-2442000908898092505883159463028000000000000)
      constant := (14194142345874547241133467338157082928013056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree014.table
  base := (1138515190155286533514078031074483446613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-342079200561773374665575085320000000000000)
      constant := (1983636571534306658231207863751587702477597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105939933795947420231/100000000000000000000)
  centralHi := (13242491724493427529/12500000000000000000)
  directionLo := (109939064946715653599/100000000000000000000)
  directionHi := (137423831183394567/125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree015.table
  base := (468909292542238548090530490519128455981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-4337110903008048189907763770110000000000000)
      constant := (24962061757689237711861834266354042508729468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree015.table
  base := (376059168891789695843467649258017071211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-364546345361783151496626318830000000000000)
      constant := (2099382654452776028644098272199604885034659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109939064946715653599/100000000000000000000)
  centralHi := (137423831183394567/125000000000000000)
  directionLo := (2275954870380922359/2000000000000000000)
  directionHi := (113797743519046117951/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree016.table
  base := (-43301246417848863576492396084559042367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-13812660873557826610030785305520000000000000)
      constant := (80178816213827088596523421336886171144956688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree016.table
  base := (-50466450907615884219362343944605146601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-77402698032358585665535510468000000000000)
      constant := (450667966314873204333305402849361730224431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2275954870380922359/2000000000000000000)
  centralHi := (113797743519046117951/100000000000000000000)
  directionLo := (117529804129399632567/100000000000000000000)
  directionHi := (14691225516174954071/12500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree017.table
  base := (-706511789605416128455364407118239948713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-14613989038091508650338279300710000000000000)
      constant := (86683060761469682689548150391716378152030108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree017.table
  base := (-386859358585530583290576559045717455303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-409480634961802705158728785850000000000000)
      constant := (2440935024239867518271121665757547500107586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117529804129399632567/100000000000000000000)
  centralHi := (14691225516174954071/12500000000000000000)
  directionLo := (121146949145917344087/100000000000000000000)
  directionHi := (15143368643239668011/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree018.table
  base := (-72043348025960471428387004841824277633/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-5138439067541730230215257765300000000000000)
      constant := (31422334298444388433975584055097485839364416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree018.table
  base := (-604806309088556274422730690505633544757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-431947779761812481989780019360000000000000)
      constant := (2658532636989557784066014309589095861872134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121146949145917344087/100000000000000000000)
  centralHi := (15143368643239668011/12500000000000000000)
  directionLo := (31164795559284440869/25000000000000000000)
  directionHi := (124659182237137763477/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree019.table
  base := (-1529032924204438071162800504708898749621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-16216645367158872730953267291090000000000000)
      constant := (102825495264221738368309669977324810007305836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree019.table
  base := (-788560524248335154976282010410963147971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-454414924561822258820831252870000000000000)
      constant := (2903241571454503009642587096156094455985802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31164795559284440869/25000000000000000000)
  centralHi := (124659182237137763477/100000000000000000000)
  directionLo := (64037567381772793789/50000000000000000000)
  directionHi := (128075134763545587579/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree020.table
  base := (-462327359564573964523226436397363015287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-17017973531692554771260761286280000000000000)
      constant := (112274702895593396896270823338533773659975568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree020.table
  base := (-472463001982623166480789631380110446257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-476882069361832035651882486380000000000000)
      constant := (3172762075668375056493342149987045338330268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64037567381772793789/50000000000000000000)
  centralHi := (128075134763545587579/100000000000000000000)
  directionLo := (8212644731736658367/6250000000000000000)
  directionHi := (131402315707786533873/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree021.table
  base := (-106225657791011017775052645382812145159/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4056000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (38943050986683613173822138084000000000000)
      linear := (-1187953446415082454104550352098000000000000)
      constant := (8169850823612535246714332787640877878470192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree021.table
  base := (-1079316822243856583368242927963416883623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-499349214161841812482933719890000000000000)
      constant := (3465264192617630354671787748703365093335426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/6250000000000000000)
  centralHi := (131402315707786533873/100000000000000000000)
  directionLo := (67323652979538409471/50000000000000000000)
  directionHi := (134647305959076818943/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree022.table
  base := (-147713267498812449584547944193179415849/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-18620629860759918851875749276660000000000000)
      constant := (133591327892401281840931920598714142943594944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree022.table
  base := (-2392085167644009591241713127184831689699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-521816358961851589313984953400000000000000)
      constant := (3779291275900879359552414649845763444440869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67323652979538409471/50000000000000000000)
  centralHi := (134647305959076818943/100000000000000000000)
  directionLo := (34453977846093551629/25000000000000000000)
  directionHi := (137815911384374206517/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree023.table
  base := (-2573004927121761325185070066701381344053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-19421958025293600892183243271850000000000000)
      constant := (145362822970170367763602369529272545902781548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree023.table
  base := (-2597070089216265231675131412440157235819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-544283503761861366145036186910000000000000)
      constant := (4113683392021068794747289662052613427146589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34453977846093551629/25000000000000000000)
  centralHi := (137815911384374206517/100000000000000000000)
  directionLo := (2818265697862720977/2000000000000000000)
  directionHi := (140913284893136048851/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree024.table
  base := (-275887867637438549873761405316592637311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4056000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (38943050986683613173822138084000000000000)
      linear := (-1348219079321818862166049151136000000000000)
      constant := (10521883517070462411165219614387900263066584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree024.table
  base := (-347382012836138803032672590639587014369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-566750648561871142976087420420000000000000)
      constant := (4467516500779296133434448623055278356573112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2818265697862720977/2000000000000000000)
  centralHi := (140913284893136048851/100000000000000000000)
  directionLo := (17993003105392525567/12500000000000000000)
  directionHi := (143944024843140204537/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree025.table
  base := (-58509935614043938827220244843925332831/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-840984574174438598911929250489200000000000)
      constant := (6838418512761284654774342563892866550112392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree025.table
  base := (-735600220497690317449361901848925410947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-589217793361880919807138653930000000000000)
      constant := (4840054155281692854579200807225126422199828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/12500000000000000000)
  centralHi := (143944024843140204537/100000000000000000000)
  directionLo := (146912255161749540709/100000000000000000000)
  directionHi := (14691225516174954071/10000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree026.table
  base := (-3076426040229817762253745696337812974307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (8025)
      previous := (0)
      next := (3675)
      square := (44934289600019553662102467020000000000000)
      linear := (-1678918655299588231777363481340000000000000)
      constant := (14210596365164439035144586183788903528024324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree026.table
  base := (-1545289546131134934134804814467595464841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-47052687550914668972168452880000000000000)
      constant := (402362241316878550252605023483842517914134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146912255161749540709/100000000000000000000)
  centralHi := (14691225516174954071/10000000000000000000)
  directionLo := (1498216911711366471/1000000000000000000)
  directionHi := (149821691171136647101/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree027.table
  base := (-3214518264716355226963855608886123935181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-7542423561142776351137739750870000000000000)
      constant := (66380924043266433608815726823870190659452932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree027.table
  base := (-1613181371255620630598714863569502710601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-634152082961900473469241120950000000000000)
      constant := (5639012976770195777531635980828508083816862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1498216911711366471/1000000000000000000)
  centralHi := (149821691171136647101/100000000000000000000)
  directionLo := (38168923529200988043/25000000000000000000)
  directionHi := (152675694116803952173/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree028.table
  base := (-835513702206704650005171585419893730481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-23428598847962011093720713247800000000000000)
      constant := (214161641205234980112664713246961466175014384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree028.table
  base := (-1675982251085969959851611482354196749263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-656619227761910250300292354460000000000000)
      constant := (6064591733099626031702841588244281498749106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38168923529200988043/25000000000000000000)
  centralHi := (152675694116803952173/100000000000000000000)
  directionLo := (155477316682261805479/100000000000000000000)
  directionHi := (3886932917056545137/2500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree029.table
  base := (-3460861721730442256851691568893719866859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-24229927012495693134028207242990000000000000)
      constant := (229783250290299123375431590561624358330029844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree029.table
  base := (-3469151614882849809728985708512882263167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-679086372561920027131343587970000000000000)
      constant := (6507146741932808125553284741536322897524777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155477316682261805479/100000000000000000000)
  centralHi := (3886932917056545137/2500000000000000000)
  directionLo := (158229341246763601947/100000000000000000000)
  directionHi := (39557335311690900487/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree030.table
  base := (-3572401508699884447910924038915139592819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-8343751725676458391445233746060000000000000)
      constant := (81999567167637625939661785164805096905763068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree030.table
  base := (-1789668232849455459379628688951700726807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-701553517361929803962394821480000000000000)
      constant := (6966439310195457201198078278834325154339234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158229341246763601947/100000000000000000000)
  centralHi := (39557335311690900487/25000000000000000000)
  directionLo := (8046715612604499999/5000000000000000000)
  directionHi := (160934312252089999981/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree031.table
  base := (-18389231375328137234200135884623896447/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-1033303333662522288585727809334800000000000)
      constant := (10512034550169823571619609977861335712131616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree031.table
  base := (-1841824303607444786960407081095050270209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-724020662161939580793446054990000000000000)
      constant := (7442278543499057749352797024144873008669358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8046715612604499999/5000000000000000000)
  centralHi := (160934312252089999981/100000000000000000000)
  directionLo := (40898640937629001537/25000000000000000000)
  directionHi := (163594563750516006149/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree032.table
  base := (-755627209427389343410637819917357862331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-5326782301219347850990137845712000000000000)
      constant := (56036803584846325174106870383238794765578196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree032.table
  base := (-756598411618219022593897279861200633899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-149297561392389871524899457700000000000000)
      constant := (1586902332538003498387341130071457092871069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40898640937629001537/25000000000000000000)
  centralHi := (163594563750516006149/100000000000000000000)
  directionLo := (83106121491425175651/50000000000000000000)
  directionHi := (166212242982850351303/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree033.table
  base := (-3874025288911922062816258340142782128011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-9145079890210140431752727741250000000000000)
      constant := (99381191284635556676654746809051687844393692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree033.table
  base := (-387809090065288443283514714605360458063/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-153790990352391826891109704402000000000000)
      constant := (1688603259571070222673731122174388165174706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83106121491425175651/50000000000000000000)
  centralHi := (166212242982850351303/100000000000000000000)
  directionLo := (33757866132834004133/20000000000000000000)
  directionHi := (84394665332085010333/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree034.table
  base := (-6345792026464000012585037904478996697/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-1129462713406564133422627088757600000000000)
      constant := (12667033781640699564734702938826944602386300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree034.table
  base := (-1984762790048152822742525104114603824161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-791422096561968911286599755520000000000000)
      constant := (8967694353756926482726181012509263907433582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33757866132834004133/20000000000000000000)
  centralHi := (84394665332085010333/50000000000000000000)
  directionLo := (171327658522279951843/100000000000000000000)
  directionHi := (42831914630569987961/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree035.table
  base := (-1013726855492479126521664416561401081589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-29037895999697785375873171214130000000000000)
      constant := (335777865909747973592306200958255493278450096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree035.table
  base := (-4057761812692786193522928422086291660051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-813889241361978688117650989030000000000000)
      constant := (9508467124344872362209251005942416709451381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171327658522279951843/100000000000000000000)
  centralHi := (42831914630569987961/25000000000000000000)
  directionLo := (10864307783149983377/6250000000000000000)
  directionHi := (173828924530399734033/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree036.table
  base := (-4140779527104610875451920400218183725917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-9946408054743822472060221736440000000000000)
      constant := (118482417632946880213744870248457523403840324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree036.table
  base := (-517896702192987919998921616312403936119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-836356386161988464948702222540000000000000)
      constant := (10065271400391022190983667688025629878367112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10864307783149983377/6250000000000000000)
  centralHi := (173828924530399734033/100000000000000000000)
  directionLo := (176294706194099448851/100000000000000000000)
  directionHi := (44073676548524862213/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree037.table
  base := (-4224052079502790735298728448989867657347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-30640552328765149456488159204510000000000000)
      constant := (375682084500148313109104721000619395172700852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree037.table
  base := (-4226061674723234885889768520182005818803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-858823530961998241779753456050000000000000)
      constant := (10638056366962941330820535029804241016622293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176294706194099448851/100000000000000000000)
  centralHi := (44073676548524862213/25000000000000000000)
  directionLo := (178726472187900264503/100000000000000000000)
  directionHi := (22340809023487533063/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree038.table
  base := (-2152489826924950774022430364029964828021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-31441880493298831496795653199700000000000000)
      constant := (396480811881284740802566764802098387972640472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree038.table
  base := (-4306667965271839803277993863221946706237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-881290675762008018610804689560000000000000)
      constant := (11226781129264690805301733535695491006645947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178726472187900264503/100000000000000000000)
  centralHi := (22340809023487533063/12500000000000000000)
  directionLo := (90562796292684015907/50000000000000000000)
  directionHi := (36225118517073606363/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree039.table
  base := (-4383767727063521080298183243286938335629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (2675)
      previous := (0)
      next := (1225)
      square := (14978096533339851220700822340000000000000)
      linear := (-826748939944423424028285825510000000000000)
      constant := (10713902177453420015117397060773487619641876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree039.table
  base := (-4385187452179294130681086168385943563651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-69519832350924445803219686390000000000000)
      constant := (910108672196233251330502455185982733672537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90562796292684015907/50000000000000000000)
  centralHi := (36225118517073606363/20000000000000000000)
  directionLo := (45873336971266031339/25000000000000000000)
  directionHi := (183493347885064125357/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree040.table
  base := (-1115145584665588204720018144238372932779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-33044536822366195577410641190080000000000000)
      constant := (439765193433912440456318627578214956307890256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree040.table
  base := (-557722175703940070582158451156239058297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-926224965362027572272907156580000000000000)
      constant := (12451924616160544781086590627636764793182456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45873336971266031339/25000000000000000000)
  centralHi := (183493347885064125357/100000000000000000000)
  directionLo := (92915468500591449297/50000000000000000000)
  directionHi := (37166187400236579719/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree041.table
  base := (-1133889455924344156135896810462233661343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-33845864986899877617718135185270000000000000)
      constant := (462249020126521758929965583434434831617556752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree041.table
  base := (-4536564852072742160432208290240319945139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-948692110162037349103958390090000000000000)
      constant := (13088295294624154650338771418704385929271509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92915468500591449297/50000000000000000000)
  centralHi := (37166187400236579719/20000000000000000000)
  directionLo := (188139484360423523223/100000000000000000000)
  directionHi := (23517435545052940403/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree042.table
  base := (-1152200751646723412807927611893152860461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-11549064383811186552675209726820000000000000)
      constant := (161764334303583463929976747697207743995940368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree042.table
  base := (-2304826264188285579811507558463031170317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-971159254962047125935009623600000000000000)
      constant := (13740507411410221406219783223579495464432854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188139484360423523223/100000000000000000000)
  centralHi := (23517435545052940403/12500000000000000000)
  directionLo := (1487656611127547637/781250000000000000)
  directionHi := (190420046224326097537/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree043.table
  base := (-4680406165421993423018247207889728426091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-35448521315967241698333123175650000000000000)
      constant := (508896604702692150371747576846032642255662356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree043.table
  base := (-58514045554855456625250816361312387223/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-198725279952411380553212171422000000000000)
      constant := (2881709380810973510634610458430011304949008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1487656611127547637/781250000000000000)
  centralHi := (190420046224326097537/100000000000000000000)
  directionLo := (48168404084487094319/25000000000000000000)
  directionHi := (192673616337948377277/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree044.table
  base := (-1187609753396886037958229728162928377683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-36249849480500923738640617170840000000000000)
      constant := (533059389198113496474037159761806975000706512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree044.table
  base := (-2375522847557409261339051828133858991851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1016093544562066679597112090620000000000000)
      constant := (15092402365901997928770326754890755660754362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48168404084487094319/25000000000000000000)
  centralHi := (192673616337948377277/100000000000000000000)
  directionLo := (97450565495295315961/50000000000000000000)
  directionHi := (194901130990590631923/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree045.table
  base := (-4818959895594248811022740609063678242269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-12350392548344868592982703722010000000000000)
      constant := (185927000476337104402318584097250110524678468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree045.table
  base := (-963894702916760658924379235116137578331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-207712137872415291285632664826000000000000)
      constant := (3158412906000173194494884231000372749262061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97450565495295315961/50000000000000000000)
  centralHi := (194901130990590631923/100000000000000000000)
  directionLo := (24637934195209975101/12500000000000000000)
  directionHi := (197103473561679800809/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree046.table
  base := (-122150408855751162416437392829178981179/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-7570501161913657563851121032244000000000000)
      constant := (116612230429012755822002958426533200628055712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree046.table
  base := (-4886451724260398981315589419119653233667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1061027834162086233259214557640000000000000)
      constant := (16507525855323885309391894725148778603510277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24637934195209975101/12500000000000000000)
  centralHi := (197103473561679800809/100000000000000000000)
  directionLo := (199281478614416769899/100000000000000000000)
  directionHi := (1992814786144167699/1000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree047.table
  base := (-495164719443901061365901110927429999669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-7730766794820393971912619831282000000000000)
      constant := (121779921051398230317533976904079781764027608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree047.table
  base := (-4952016697785664617345817030284843839867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1083494978962096010090265791150000000000000)
      constant := (17238780194725716962677606379596861391062477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199281478614416769899/100000000000000000000)
  centralHi := (1992814786144167699/1000000000000000000)
  directionLo := (8057437423639522237/4000000000000000000)
  directionHi := (100717967795494027963/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree048.table
  base := (-2507942072036272952389522964638231458963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-13151720712878550633290197717200000000000000)
      constant := (211765389244181828061673108965507333202446072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree048.table
  base := (-1003239627813630470162235264370846443803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-221192424752421157384263404932000000000000)
      constant := (3597164505649163123860578634497326950997293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8057437423639522237/4000000000000000000)
  centralHi := (100717967795494027963/50000000000000000000)
  directionLo := (12722974509733662681/6250000000000000000)
  directionHi := (203567592155738602897/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree049.table
  base := (-126968829787961444353117396720630210789/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-8051298060633866788035617429358000000000000)
      constant := (132450136291675073764695109809738236380477792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree049.table
  base := (-2539510175538954843983320090956208068899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1128429268562115563752368258170000000000000)
      constant := (18748648748682243250710664685731801672712138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/6250000000000000000)
  centralHi := (203567592155738602897/100000000000000000000)
  directionLo := (205677157226449356993/100000000000000000000)
  directionHi := (102838578613224678497/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree050.table
  base := (-5140275664154176212148932784781868043637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-41057818467703015980485581141980000000000000)
      constant := (689763016678716521441122670199762114822512492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree050.table
  base := (-642562907129560402318263863654314457773/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1150896413362125340583419491680000000000000)
      constant := (19527255489010558483235891430839366853090904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205677157226449356993/100000000000000000000)
  centralHi := (102838578613224678497/50000000000000000000)
  directionLo := (207765303728562939127/100000000000000000000)
  directionHi := (25970662966070367391/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree051.table
  base := (-1300117274690083918023875380202425186817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-13953048877412232673597691712390000000000000)
      constant := (239277688899931854008141915573629176884540496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree051.table
  base := (-5200663223234869967020925600892786844791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1173363558162135117414470725190000000000000)
      constant := (20321639983327582819742917438404119023230321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207765303728562939127/100000000000000000000)
  centralHi := (25970662966070367391/12500000000000000000)
  directionLo := (209832671102691845131/100000000000000000000)
  directionHi := (52458167775672961283/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree052.table
  base := (-1051869588961808420603999187768831851167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 936000000000000000000000000000000000000000
      center := (1605)
      previous := (0)
      next := (735)
      square := (8986857920003910732420493404000000000000)
      linear := (-656314996873390462478470294344000000000000)
      constant := (11484011440169603045835854547016186693653844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree052.table
  base := (-1051902744557872004378386781988701398941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (20)
      square := (249634942222330853678347039000000000000)
      linear := (-18397395430186844526854183980000000000000)
      constant := (325104614687333280542693832570146881813767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209832671102691845131/100000000000000000000)
  centralHi := (52458167775672961283/25000000000000000000)
  directionLo := (211879867591894840463/100000000000000000000)
  directionHi := (13242491724493427529/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree053.table
  base := (-5316924133381469879257696121286229579639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-43461802961304062101408063127550000000000000)
      constant := (775645974823704564412381222683928329237476324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree053.table
  base := (-2658532935871004939021477764567858367049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1218297847762154671076573192210000000000000)
      constant := (21957733524446692182197070938731063871937438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211879867591894840463/100000000000000000000)
  centralHi := (13242491724493427529/6250000000000000000)
  directionLo := (13369217020744446221/6250000000000000000)
  directionHi := (213907472331911139537/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree054.table
  base := (-5373207537953236848045146102374029525367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-14754377041945914713905185707580000000000000)
      constant := (268462900089203667446996881400070468122555724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree054.table
  base := (-5373328862614595249535111099859758679449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1240764992562164447907624425720000000000000)
      constant := (22799439139101489564832503515023700783173119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13369217020744446221/6250000000000000000)
  centralHi := (213907472331911139537/100000000000000000000)
  directionLo := (53979009316177576701/25000000000000000000)
  directionHi := (43183207452942061361/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree055.table
  base := (-5428206348079995154190898893923757072293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-45064459290371426182023051117930000000000000)
      constant := (835688870117486924116143573581011611972169388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree055.table
  base := (-5428310315503903318370893923271832006843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1263232137362174224738675659230000000000000)
      constant := (23656915510844698349422975478042060390843533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53979009316177576701/25000000000000000000)
  centralHi := (43183207452942061361/20000000000000000000)
  directionLo := (108953044446637894361/50000000000000000000)
  directionHi := (217906088893275788723/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree056.table
  base := (-2740963686427227629465720146246415524503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-45865787454905108222330545113120000000000000)
      constant := (866546442946812279291677231240073615897847496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree056.table
  base := (-2741008281400620827243698381122402832669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1285699282162184001569726892740000000000000)
      constant := (24530161569502187556649118150860627842557878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108953044446637894361/50000000000000000000)
  centralHi := (217906088893275788723/100000000000000000000)
  directionLo := (109939064946715653599/50000000000000000000)
  directionHi := (219878129893431307199/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree057.table
  base := (-5534376287678270241786993452925297460693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-15555705206479596754212679702770000000000000)
      constant := (299320461408814470177263526501108746749714596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree057.table
  base := (-5534452880422758034052319627731126285049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1308166426962193778400778126250000000000000)
      constant := (25419176423444128212338590231628439657826719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109939064946715653599/50000000000000000000)
  centralHi := (219878129893431307199/100000000000000000000)
  directionLo := (221832640596691925179/100000000000000000000)
  directionHi := (11091632029834596259/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree058.table
  base := (-2792778917614740383619452434317391747203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-47468443783972472302945533103500000000000000)
      constant := (929933665101927118433779106304840977220033896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree058.table
  base := (-2792811837942408944992833580643165796203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1330633571762203555231829359760000000000000)
      constant := (26323959327800254558327910935922609960883386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221832640596691925179/100000000000000000000)
  centralHi := (11091632029834596259/5000000000000000000)
  directionLo := (55942520089133414569/25000000000000000000)
  directionHi := (223770080356533658277/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree059.table
  base := (-1127095197874881460146872002653021602207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-9653954389701230868650605419738000000000000)
      constant := (192492652279252141857172427044593766572172612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree059.table
  base := (-5635532641519287652833255549606372807803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1353100716562213332062880593270000000000000)
      constant := (27244509658566481167854837328191522995481293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55942520089133414569/25000000000000000000)
  centralHi := (223770080356533658277/100000000000000000000)
  directionLo := (22569088880909209353/10000000000000000000)
  directionHi := (225690888809092093531/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree060.table
  base := (-5684134089065058542070357769996506088429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-16357033371013278794520173697960000000000000)
      constant := (331850050931753387386158241684147085652665988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree060.table
  base := (-568418287949295996620203435166673033671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-275113572272444621778786365356000000000000)
      constant := (5636165378295324016829958986593664514619202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22569088880909209353/10000000000000000000)
  centralHi := (225690888809092093531/100000000000000000000)
  directionLo := (2275954870380922359/1000000000000000000)
  directionHi := (227595487038092235901/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree061.table
  base := (-1432883736973516938117074669498890479207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-49872428277573518423868015089070000000000000)
      constant := (1029194322181027896290345874912968751298018448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree061.table
  base := (-2865788501995336651893568036474828037657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1398035006162232885724983060290000000000000)
      constant := (29132910584733433605158306356826508123271934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2275954870380922359/1000000000000000000)
  centralHi := (227595487038092235901/100000000000000000000)
  directionLo := (22948427865275401289/10000000000000000000)
  directionHi := (229484278652754012891/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree062.table
  base := (-5777680943880899261877564977281329230981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-50673756442107200464175509084260000000000000)
      constant := (1063395755085693490698063543256275392958711596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree062.table
  base := (-2888858612438496216687023931175665379461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1420502150962242662556034293800000000000000)
      constant := (30100760364869810285124624271602625101742182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22948427865275401289/10000000000000000000)
  centralHi := (229484278652754012891/100000000000000000000)
  directionLo := (231357650786489642139/100000000000000000000)
  directionHi := (11567882539324482107/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree063.table
  base := (-1455643523295340618980821447289175817711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-17158361535546960834827667693150000000000000)
      constant := (366051479747655000319268148169451455766728368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree063.table
  base := (-2911302708157072878664492483571872170651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1442969295762252439387085527310000000000000)
      constant := (31084375915152333524048858300507707206319962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231357650786489642139/100000000000000000000)
  centralHi := (11567882539324482107/5000000000000000000)
  directionLo := (233215975023392708219/100000000000000000000)
  directionHi := (11660798751169635411/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree064.table
  base := (-5866216110704059113711044535262977162551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-52276412771174564544790497074640000000000000)
      constant := (1133470364219338494210530209131940046943039716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree064.table
  base := (-5866243173142469168708439643955478280967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1465436440562262216218136760820000000000000)
      constant := (32083756966052986556004461252171524170516577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233215975023392708219/100000000000000000000)
  centralHi := (11660798751169635411/5000000000000000000)
  directionLo := (47011921651759853027/20000000000000000000)
  directionHi := (14691225516174954071/6250000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree065.table
  base := (-369288028752982939990282317623382532759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (8025)
      previous := (0)
      next := (3675)
      square := (44934289600019553662102467020000000000000)
      linear := (-4082903148900634352699845466910000000000000)
      constant := (89949501623867634560614774858154861594700608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree065.table
  base := (-5908631857290590946807610902579027935997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-114454121950943999465322153410000000000000)
      constant := (2546069483646602400137734191841472636832039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47011921651759853027/20000000000000000000)
  centralHi := (14691225516174954071/6250000000000000000)
  directionLo := (47377778699913153221/20000000000000000000)
  directionHi := (118444446749782883053/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree066.table
  base := (-5949752394714942172492729797367363774787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-17959689700080642875135161688340000000000000)
      constant := (401924634096492531434683226719063986264731964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree066.table
  base := (-5949772636049474399980733406971634882219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1510370730162281769880239227840000000000000)
      constant := (34129814681938694662295242367601793704904989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47377778699913153221/20000000000000000000)
  centralHi := (118444446749782883053/50000000000000000000)
  directionLo := (11935208030457308713/5000000000000000000)
  directionHi := (238704160609146174261/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree067.table
  base := (-1497412248047063741581613678320739380291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-54680397264775610665712979060210000000000000)
      constant := (1242761501201529692292486053093760236441238224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree067.table
  base := (-1497416628424014267645939238100483898061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1532837874962291546711290461350000000000000)
      constant := (35176490979928774492860399357759072884910764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11935208030457308713/5000000000000000000)
  centralHi := (238704160609146174261/100000000000000000000)
  directionLo := (240505727002051849771/100000000000000000000)
  directionHi := (60126431750512962443/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree068.table
  base := (-3014149591078474242131164705219333956841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-55481725429309292706020473055400000000000000)
      constant := (1280306312190205945098516368924631144413158712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree068.table
  base := (-6028314357671708474549012277622425131133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1555305019762301323542341694860000000000000)
      constant := (36238932034778479245293451569561810152838523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240505727002051849771/100000000000000000000)
  centralHi := (60126431750512962443/25000000000000000000)
  directionLo := (9691755931673387527/4000000000000000000)
  directionHi := (15143368643239668011/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree069.table
  base := (-3032851884971058753672253214572252104971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-18761017864614324915442655683530000000000000)
      constant := (439469443451977604024756001198186195462237624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree069.table
  base := (-6065716920294599586390522144793029831379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1577772164562311100373392928370000000000000)
      constant := (37317137719346038024901529156204977958496949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9691755931673387527/4000000000000000000)
  centralHi := (15143368643239668011/6250000000000000000)
  directionLo := (1906788819502652893/781250000000000000)
  directionHi := (48813793779267914061/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree070.table
  base := (-6101863455973404262327156390911152638347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-57084381758376656786635461045780000000000000)
      constant := (1357067551437296349912168583042271547348296852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree070.table
  base := (-381367178550160996610446025797959305289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1600239309362320877204444161880000000000000)
      constant := (38411107922896254935482286491542318038498544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1906788819502652893/781250000000000000)
  centralHi := (48813793779267914061/20000000000000000000)
  directionLo := (245831222603620496231/100000000000000000000)
  directionHi := (30728902825452562029/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree071.table
  base := (-30683894260067277948493867835707474943/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-2315428396916413553077718201638800000000000)
      constant := (55851358868493304609387444324822195779574304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree071.table
  base := (-49094309923005220598846879186186074539/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67600000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (52)
      square := (649050849778060219563702301400000000000)
      linear := (-64908258166493226161419815815600000000000)
      constant := (1580833701942468297531512390461872767014545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245831222603620496231/100000000000000000000)
  centralHi := (30728902825452562029/12500000000000000000)
  directionLo := (9903237324064025719/4000000000000000000)
  directionHi := (7736904159425020093/3125000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree072.table
  base := (-1542612623674688327444846522227555696697/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-19562346029148006955750149678720000000000000)
      constant := (478685862638715084215664509226650068188393936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree072.table
  base := (-6170459074667925395115449379751442650987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1645173598962340430866546628900000000000000)
      constant := (40646341511224853322591569070662006191983197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9903237324064025719/4000000000000000000)
  centralHi := (7736904159425020093/3125000000000000000)
  directionLo := (249318364474275526953/100000000000000000000)
  directionHi := (124659182237137763477/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree073.table
  base := (-6202878856862113162285001663657704208943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-59488366251977702907557943031350000000000000)
      constant := (1476388397172019411188658650828390277592790788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree073.table
  base := (-3101443152141008242454413794767268657717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1667640743762350207697597862410000000000000)
      constant := (41787604735747849457150230477123663193691654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249318364474275526953/100000000000000000000)
  centralHi := (124659182237137763477/50000000000000000000)
  directionLo := (50208754333401315061/20000000000000000000)
  directionHi := (125521885833503287653/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree074.table
  base := (-779258044627274212160401345717737428739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-60289694416511384947865437026540000000000000)
      constant := (1517276396933711908241070257119881283868415392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree074.table
  base := (-6234070823540731074268969017215753857883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1690107888562359984528649095920000000000000)
      constant := (42944632155490141758088221292190537598017773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50208754333401315061/20000000000000000000)
  centralHi := (125521885833503287653/50000000000000000000)
  directionLo := (252757400923226328227/100000000000000000000)
  directionHi := (63189350230806582057/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree075.table
  base := (-6264007367325067771865276713196301870953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-20363674193681688996057643673910000000000000)
      constant := (519573861645671009513895033509169149805707316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree075.table
  base := (-6264012983846869124715912296898407042147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1712575033362369761359700329430000000000000)
      constant := (44117423711064657031908654986699169209877157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252757400923226328227/100000000000000000000)
  centralHi := (63189350230806582057/25000000000000000000)
  directionLo := (12722974509733662681/5000000000000000000)
  directionHi := (254459490194673253621/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree076.table
  base := (-251708328811171310291926375365205059221/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-2475694029823149961139217000676800000000000)
      constant := (64028958366360551115348599886114092419699436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree076.table
  base := (-6292713099870268898587100624112621212281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1735042178162379538190751562940000000000000)
      constant := (45305979349292192612276503660604967015124511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/5000000000000000000)
  centralHi := (254459490194673253621/100000000000000000000)
  directionLo := (256150269527091175157/100000000000000000000)
  directionHi := (128075134763545587579/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree077.table
  base := (-316008360717822792583259621849848051631/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-12538735782022486213757583802422000000000000)
      constant := (328656703556757700246804189003576847815507984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree077.table
  base := (-3160085727379443875734044780501370532047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1757509322962389315021802796450000000000000)
      constant := (46510299022320743706097808423905536760168114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256150269527091175157/100000000000000000000)
  centralHi := (128075134763545587579/50000000000000000000)
  directionLo := (128914980711581668053/50000000000000000000)
  directionHi := (257829961423163336107/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree078.table
  base := (-1269276923754474729137363198569910929867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312000000000000000000000000000000000000000
      center := (535)
      previous := (0)
      next := (245)
      square := (2995619306667970244140164468000000000000)
      linear := (-325615420895621092867155964140000000000000)
      constant := (8648206457299632579357229673980093894940748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree078.table
  base := (-317319415226810840688872882781121259597/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (20)
      square := (249634942222330853678347039000000000000)
      linear := (-27384253350190755259274677384000000000000)
      constant := (734313579798189850958951223107381694500956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128914980711581668053/50000000000000000000)
  centralHi := (257829961423163336107/100000000000000000000)
  directionLo := (129749390592151081451/50000000000000000000)
  directionHi := (259498781184302162903/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree079.table
  base := (-63713606775092235436891308504456141673/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2433600000000000000000000000000000000000000
      center := (4173)
      previous := (0)
      next := (1911)
      square := (23365830592010167904293282850400000000000)
      linear := (-2571853409567191805976116280099600000000000)
      constant := (69202967273741828197508460964716505336245872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree079.table
  base := (-6371363881819109099828942048921634537543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1802443612562408868683905263470000000000000)
      constant := (48966230303664734271559545318007243763155233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129749390592151081451/50000000000000000000)
  centralHi := (259498781184302162903/100000000000000000000)
  directionLo := (261156937232781113871/100000000000000000000)
  directionHi := (16322308577048819617/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree080.table
  base := (-3197547806363357515580856072618908965639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-65097663403713477189710400997680000000000000)
      constant := (1774305284442520884613457582969173115706104648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree080.table
  base := (-6395098398966989097935320285950638341979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1824910757362418645514956496980000000000000)
      constant := (50217841836779182845256096466874342120205549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261156937232781113871/100000000000000000000)
  centralHi := (16322308577048819617/6250000000000000000)
  directionLo := (8212644731736658367/3125000000000000000)
  directionHi := (52560926283114613549/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree081.table
  base := (-802198703457178830435796666817994784341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-21966330522749053076672631664290000000000000)
      constant := (606364521911295619952211669968526102618851616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree081.table
  base := (-6417592050754449828374493385434545303027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1847377902162428422346007730490000000000000)
      constant := (51485217253308779812994517676416561843788437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/3125000000000000000)
  centralHi := (52560926283114613549/20000000000000000000)
  directionLo := (66110514822787293319/25000000000000000000)
  directionHi := (264442059291149173277/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree082.table
  base := (-6438842909068954899177845973758615356697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-66700319732780841270325388988060000000000000)
      constant := (1864439024581349646456600178144107584169855452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree082.table
  base := (-6438845016643658684422711585274851860357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1869845046962438199177058964000000000000000)
      constant := (52768356522924418885311122656428550035599667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66110514822787293319/25000000000000000000)
  centralHi := (264442059291149173277/100000000000000000000)
  directionLo := (259833408594132571/97656250000000000)
  directionHi := (53213882080078350541/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree083.table
  base := (-40367847683509354783872406172990930523/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-13500329579462904662126576596650000000000000)
      constant := (382068331987205274611401789584459491718338176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree083.table
  base := (-6458857462720162008315447288164582481763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1892312191762447976008110197510000000000000)
      constant := (54067259617557642730368116570855185560582053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259833408594132571/97656250000000000)
  centralHi := (53213882080078350541/20000000000000000000)
  directionLo := (133843434261341836623/50000000000000000000)
  directionHi := (267686868522683673247/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree084.table
  base := (-3238813974179153198307191700561214312791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-22767658687282735116980125659480000000000000)
      constant := (652267156941850795239491575492383714747319704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree084.table
  base := (-6477629543345095138269265597639382749271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1914779336562457752839161431020000000000000)
      constant := (55381926511121419476006899917198944315373201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133843434261341836623/50000000000000000000)
  centralHi := (267686868522683673247/100000000000000000000)
  directionLo := (67323652979538409471/25000000000000000000)
  directionHi := (53858922383630727577/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree085.table
  base := (-3247580007418375471387321643799056710789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-69104304226381887391247870973630000000000000)
      constant := (2003818456344766182700322059593446827943119448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree085.table
  base := (-811895175321007517339925056913006103437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1937246481362467529670212664530000000000000)
      constant := (56712357179271366373337918159328615748153176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67323652979538409471/25000000000000000000)
  centralHi := (53858922383630727577/20000000000000000000)
  directionLo := (135446406778490635169/50000000000000000000)
  directionHi := (270892813556981270339/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree086.table
  base := (-6511451967840100495077834213416315437999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-69905632390915569431555364968820000000000000)
      constant := (2051392615647728508767827222429750136875214084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree086.table
  base := (-6511453175337695239181794712435954853999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-1959713626162477306501263898040000000000000)
      constant := (58058551599201163561572976955378323629674169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135446406778490635169/50000000000000000000)
  centralHi := (270892813556981270339/100000000000000000000)
  directionLo := (27248164133659694269/10000000000000000000)
  directionHi := (272481641336596942691/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree087.table
  base := (-101976624028181148879214579740711006211/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-23568986851816417157287619654670000000000000)
      constant := (699841315980290457680212302725134887081861888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree087.table
  base := (-1305300997708191597811814660990410026329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-396436154192497416666463026310000000000000)
      constant := (11884101949893383042972606538235620705550399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27248164133659694269/10000000000000000000)
  centralHi := (272481641336596942691/100000000000000000000)
  directionLo := (54812251657509672459/20000000000000000000)
  directionHi := (34257657285943545287/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree088.table
  base := (-327015802376148253284219233373567626133/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-14301657743996586702434070591840000000000000)
      constant := (429642490495421104727357357763068858250427312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree088.table
  base := (-6540316961897158333677476738594411376267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2004647915762496860163366365060000000000000)
      constant := (60798231609836057952447950721257544477410877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54812251657509672459/20000000000000000000)
  centralHi := (34257657285943545287/12500000000000000000)
  directionLo := (34453977846093551629/12500000000000000000)
  directionHi := (275631822768748413033/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree089.table
  base := (-3276444206494568643916584827057413452223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-72309616884516615552477846954390000000000000)
      constant := (2197458128550742190010045623875689143113350536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree089.table
  base := (-6552889208728628880410545144213523810759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2027115060562506636994417598570000000000000)
      constant := (62191717161157117563681602763502914475981729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34453977846093551629/12500000000000000000)
  centralHi := (275631822768748413033/100000000000000000000)
  directionLo := (138596744326383056873/50000000000000000000)
  directionHi := (277193488652766113747/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree090.table
  base := (-3282110572054516870851391197058646619157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-24370315016350099197595113649860000000000000)
      constant := (749086991831035883100182121682655129312699208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree090.table
  base := (-1641055459156615268367820834486013117589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2049582205362516413825468832080000000000000)
      constant := (63600966385247199594491991003987455132509836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138596744326383056873/50000000000000000000)
  centralHi := (277193488652766113747/100000000000000000000)
  directionLo := (69686601375443586973/25000000000000000000)
  directionHi := (278746405501774347893/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree091.table
  base := (-6574314345329355608470379466479110425109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (8025)
      previous := (0)
      next := (3675)
      square := (44934289600019553662102467020000000000000)
      linear := (-5685559477967998433314833457290000000000000)
      constant := (176740076359134474732462091669656526321048988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree091.table
  base := (-821789368503356000301479253776874758801/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-159388411550963553127424620430000000000000)
      constant := (5001998404984199031749600255742205025084696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69686601375443586973/25000000000000000000)
  centralHi := (278746405501774347893/100000000000000000000)
  directionLo := (140145359367361908223/50000000000000000000)
  directionHi := (280290718734723816447/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree092.table
  base := (-6583168116177545824434099643512067916247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-74713601378117661673400328939960000000000000)
      constant := (2348538179472138793849990227557652578797553252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree092.table
  base := (-822896080088894867367383560274350188069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2094516494962535967487571299100000000000000)
      constant := (66466755783274229611521578482349078545730712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140145359367361908223/50000000000000000000)
  centralHi := (280290718734723816447/100000000000000000000)
  directionLo := (281826569786272097701/100000000000000000000)
  directionHi := (140913284893136048851/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree093.table
  base := (-3295391275865988657260506318658385753391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-25171643180883781237902607645050000000000000)
      constant := (800004178441607565136413060158632837384246104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree093.table
  base := (-3295391504120423413930565136545272585033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2116983639762545744318622532610000000000000)
      constant := (67923295924874240643149740212202697866258846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281826569786272097701/100000000000000000000)
  centralHi := (140913284893136048851/50000000000000000000)
  directionLo := (141677048128979713889/50000000000000000000)
  directionHi := (283354096257959427779/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree094.table
  base := (-1319431548606312739531854260006905166459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-15263251541437005150803063386068000000000000)
      constant := (490408811934583825148439033701568988967263444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree094.table
  base := (-6597158140336591574746875055827517715973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2139450784562555521149673766120000000000000)
      constant := (69395599674431825603588151908865149506000563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141677048128979713889/50000000000000000000)
  centralHi := (283354096257959427779/100000000000000000000)
  directionLo := (284873432062088543889/100000000000000000000)
  directionHi := (28487343206208854389/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree095.table
  base := (-41264336108959035304836540328095547271/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-15423517174343741558864562185106000000000000)
      constant := (500926550396989448196522933835912484092903552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree095.table
  base := (-3301147061604827241490386837981054954829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2161917929362565297980724999630000000000000)
      constant := (70883667017377281332564837999437403425267798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284873432062088543889/100000000000000000000)
  centralHi := (28487343206208854389/10000000000000000000)
  directionLo := (57276941511746877617/20000000000000000000)
  directionHi := (143192353779367194043/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree096.table
  base := (-3303095369463052514090791062589684025519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-25972971345417463278210101640240000000000000)
      constant := (852592870583307039164110001136536241592494936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree096.table
  base := (-1651547759963054387254044392979351180151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2184385074162575074811776233140000000000000)
      constant := (72387497939684929072679182090825958602217924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57276941511746877617/20000000000000000000)
  centralHi := (143192353779367194043/50000000000000000000)
  directionLo := (17993003105392525567/6250000000000000000)
  directionHi := (287888049686280409073/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree097.table
  base := (-3304424354202080855244205546765375100127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-78720242200786071874937798915910000000000000)
      constant := (2611481638475677887954238676192182665781654664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree097.table
  base := (-660884897029246828953312669214058518939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-441370443792516970328565493330000000000000)
      constant := (14781418485566001026722451486348648220598618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/6250000000000000000)
  centralHi := (287888049686280409073/100000000000000000000)
  directionLo := (36172947760731425521/12500000000000000000)
  directionHi := (289383582085851404169/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree098.table
  base := (-6610267763910181461034846568661739092573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-79521570365319753915245292911100000000000000)
      constant := (2665741831687406582252009005150876979360785868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree098.table
  base := (-66102679918193355124370710797741586979/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67600000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (52)
      square := (649050849778060219563702301400000000000)
      linear := (-89172774550503785138955148006400000000000)
      constant := (3017698018750027221873121718595926687202196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36172947760731425521/12500000000000000000)
  centralHi := (289383582085851404169/100000000000000000000)
  directionLo := (145435712609994057389/50000000000000000000)
  directionHi := (290871425219988114779/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree099.table
  base := (-1322089596169607917720778704784812313039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4056000000000000000000000000000000000000000
      center := (6955)
      previous := (0)
      next := (3185)
      square := (38943050986683613173822138084000000000000)
      linear := (-5354859901990229063703519127086000000000000)
      constant := (181370612728423334867133679201854650629156908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree099.table
  base := (-1652612044795264593907412310198466993167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2251786508562604405304929933670000000000000)
      constant := (76993572049814502894641161782780836312619108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145435712609994057389/50000000000000000000)
  centralHi := (290871425219988114779/100000000000000000000)
  directionLo := (292351696485885947883/100000000000000000000)
  directionHi := (73087924121471486971/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree100.table
  base := (-3304694716085860742274084239083448252397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-81124226694387117995860280901480000000000000)
      constant := (2775933715748656163098237905922332601664833304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree100.table
  base := (-1321877920952231789380633011885434844497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-454850730672522836427196233436000000000000)
      constant := (15712091431757731389518942905791361511280007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292351696485885947883/100000000000000000000)
  centralHi := (73087924121471486971/25000000000000000000)
  directionLo := (146912255161749540709/50000000000000000000)
  directionHi := (293824510323499081419/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree101.table
  base := (-660709218855287842168826675906134745989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-16385110971784160007233554979334000000000000)
      constant := (566373081144871735236373331372172902410805848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree101.table
  base := (-3303546169367434795189442522896055204071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2296720798162623958967032400690000000000000)
      constant := (80143105783813528436152207163216133341024002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146912255161749540709/50000000000000000000)
  centralHi := (293824510323499081419/100000000000000000000)
  directionLo := (295289978318791676621/100000000000000000000)
  directionHi := (147644989159395838311/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree102.table
  base := (-825444539816247398343138587629400564107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-27575627674484827358825089630620000000000000)
      constant := (962784753478823172719827120509585605247928032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree102.table
  base := (-6603556449208626104785453393455526074031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2319187942962633735798083634200000000000000)
      constant := (81741517913379129710328498816846016093488761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295289978318791676621/100000000000000000000)
  centralHi := (147644989159395838311/50000000000000000000)
  directionLo := (296748209302399832757/100000000000000000000)
  directionHi := (148374104651199916379/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree103.table
  base := (-1319756377728298387647248367630659048343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-16705642237597632823356552577410000000000000)
      constant := (589080055896033729750932252145751820349881188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree103.table
  base := (-824847750293107912803779405039026023629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2341655087762643512629134867710000000000000)
      constant := (83355693536304009286843644781542236816053592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296748209302399832757/100000000000000000000)
  centralHi := (148374104651199916379/50000000000000000000)
  directionLo := (298199309443951158891/100000000000000000000)
  directionHi := (74549827360987789723/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree104.table
  base := (-6592768963545184972659913342666023210303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (8025)
      previous := (0)
      next := (3675)
      square := (44934289600019553662102467020000000000000)
      linear := (-6486887642501680473622327452480000000000000)
      constant := (231000266343236785050116232204992301137578196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree104.table
  base := (-6592769062474031333985906322919178741423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-181855556350973329958475853940000000000000)
      constant := (6537356357055101622325689450602050676361501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298199309443951158891/100000000000000000000)
  centralHi := (74549827360987789723/25000000000000000000)
  directionLo := (1498216911711366471/500000000000000000)
  directionHi := (299643382342273294201/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree105.table
  base := (-6585517606125340505118824172962768192059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-28376955839018509399132583625810000000000000)
      constant := (1020387936333203405284448600902112756106504348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree105.table
  base := (-6585517692195479892980948287738768154307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2386589377362663066291237334730000000000000)
      constant := (86631335219036775022293139647447148181922117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1498216911711366471/500000000000000000)
  centralHi := (299643382342273294201/100000000000000000000)
  directionLo := (301080529111708283487/100000000000000000000)
  directionHi := (9408766534740883859/3125000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree106.table
  base := (-6577027877589424285827754868714082856173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-85932195681589210237705244872620000000000000)
      constant := (3119881318720378457735858888049718519903043468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree106.table
  base := (-1644256988117156555818943600399592940027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2409056522162672843122288568240000000000000)
      constant := (88292801257963229568808765308309875172541748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301080529111708283487/100000000000000000000)
  centralHi := (9408766534740883859/3125000000000000000)
  directionLo := (302510848464736317739/100000000000000000000)
  directionHi := (15125542423236815887/5000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree107.table
  base := (-6567299837555539289827974127145127060747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-86733523846122892278012738867810000000000000)
      constant := (3179155991261666392798899195941122796962415252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree107.table
  base := (-1641824975673906376790858202575433113093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2431523666962682619953339801750000000000000)
      constant := (89970030748456720503973314703774007215549132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree107.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302510848464736317739/100000000000000000000)
  centralHi := (15125542423236815887/5000000000000000000)
  directionLo := (303934436791099898473/100000000000000000000)
  directionHi := (151967218395549949237/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree108.table
  base := (-6556333544131808284083443019780485617209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-29178284003552191439440077621000000000000000)
      constant := (1079662608756648067376085995740465175168300148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree108.table
  base := (-1311266720159318719928823437364462856241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 338000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (260)
      square := (3245254248890301097818511507000000000000)
      linear := (-490798162352538479356878207052000000000000)
      constant := (18332604736145749649658351020621405777295271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree108.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303934436791099898473/100000000000000000000)
  centralHi := (151967218395549949237/50000000000000000000)
  directionLo := (38168923529200988043/12500000000000000000)
  directionHi := (61070277646721580869/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree109.table
  base := (-3272064526994336557310287887852256211261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-88336180175190256358627726858190000000000000)
      constant := (3299376823400428917532710557720787496421376152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree109.table
  base := (-6544129103278287869960543398544236234171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2476457956562702173615442268770000000000000)
      constant := (93371780045229670806362067524721024076425101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree109.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38168923529200988043/12500000000000000000)
  centralHi := (61070277646721580869/20000000000000000000)
  directionLo := (9586306086274633143/3125000000000000000)
  directionHi := (306761794760788260577/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree110.table
  base := (-1306137284484992823118805486585865699227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12168000000000000000000000000000000000000000
      center := (20865)
      previous := (0)
      next := (9555)
      square := (116829152960050839521466414252000000000000)
      linear := (-17827501667944787679787044170676000000000000)
      constant := (672064596463336491051851997237606593085902932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree110.table
  base := (-6530686465297028462916977182417955462137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2498925101362711950446493502280000000000000)
      constant := (95096299832638070073712331059071365526898847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree110.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9586306086274633143/3125000000000000000)
  centralHi := (306761794760788260577/100000000000000000000)
  directionLo := (308165746236547873887/100000000000000000000)
  directionHi := (9630179569892121059/3125000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree111.table
  base := (-6363286819754372833534828292754384581/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-29979612168085873479747571616190000000000000)
      constant := (1140608767563414353811716687594010416663405568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree111.table
  base := (-6516005740716536512944436683384211452881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2521392246162721727277544735790000000000000)
      constant := (96836583033850977178623703639663068264463111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree111.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308165746236547873887/100000000000000000000)
  centralHi := (9630179569892121059/3125000000000000000)
  directionLo := (77390832621747285137/25000000000000000000)
  directionHi := (309563330486989140549/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree112.table
  base := (-6500086949731701935652496254347703629053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-90740164668791302479550208843760000000000000)
      constant := (3483886784200286280144062345068228571120841548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree112.table
  base := (-3250043491080637560413359297837617980851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2543859390962731504108595969300000000000000)
      constant := (98592629639974857857063723625170885122472362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree112.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77390832621747285137/25000000000000000000)
  centralHi := (309563330486989140549/100000000000000000000)
  directionLo := (155477316682261805479/50000000000000000000)
  directionHi := (310954633364523610959/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree113.table
  base := (-6482930212863242673455926548046158075803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-91541492833324984519857702838950000000000000)
      constant := (3546504426533312071900832450001270924266814548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree113.table
  base := (-3241465120532900511265513774524979495719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2566326535762741280939647202810000000000000)
      constant := (100364439642317272020653933433165556930446978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree113.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155477316682261805479/50000000000000000000)
  centralHi := (310954633364523610959/100000000000000000000)
  directionLo := (312339738809415252809/100000000000000000000)
  directionHi := (31233973880941525281/10000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree114.table
  base := (-6464535543195434328356089117739521419681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (34775)
      previous := (0)
      next := (15925)
      square := (194715254933418065869110690420000000000000)
      linear := (-30780940332619555520055065611380000000000000)
      constant := (1203226409794285051540339152643509250560886932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree114.table
  base := (-6464535567720567963541628380781139164751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2588793680562751057770698436320000000000000)
      constant := (102152013032379132986407492306147987481157081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree114.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312339738809415252809/100000000000000000000)
  centralHi := (31233973880941525281/10000000000000000000)
  directionLo := (156859364454439076397/50000000000000000000)
  directionHi := (62743745781775630559/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree115.table
  base := (-6444902989988550864812619255443088283161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-93144149162392348600472690829330000000000000)
      constant := (3673411192449216021504844947739378000885248476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree115.table
  base := (-6444903011314565245295007710907148276373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2611260825362760834601749669830000000000000)
      constant := (103955349801847501562381634005331691941292963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree115.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156859364454439076397/50000000000000000000)
  centralHi := (62743745781775630559/20000000000000000000)
  directionLo := (39386460494230799227/12500000000000000000)
  directionHi := (315091683953846393817/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree116.table
  base := (-3212016300715991492983535636932057740113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (104325)
      previous := (0)
      next := (47775)
      square := (584145764800254197607332071260000000000000)
      linear := (-93945477326926030640780184824520000000000000)
      constant := (3737700315439210419514401702989310721418305016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree116.table
  base := (-3212016309987562688232419440166647668809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2925)
      previous := (0)
      next := (1300)
      square := (16226271244451505489092557535000000000000)
      linear := (-2633727970162770611432800903340000000000000)
      constant := (105774449942588858554610507736103673087942558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree116.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39386460494230799227/12500000000000000000)
  centralHi := (315091683953846393817/100000000000000000000)
  directionLo := (158229341246763601947/50000000000000000000)
  directionHi := (63291736498705440779/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree117.table
  base := (-400120276542668662112622203290555292367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (2675)
      previous := (0)
      next := (1225)
      square := (14978096533339851220700822340000000000000)
      linear := (-2429405269011787504643273815890000000000000)
      constant := (97501194822203470664975029034763023990251968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree117.table
  base := (-6401924440805192086724685687246039508257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (100)
      square := (1248174711111654268391735195000000000000)
      linear := (-204322701150983106789527087450000000000000)
      constant := (8277639495895600497906098555120801486392659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree117.checked
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
end ForestUnimodality.Stage170KernelData.Cell347.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell347
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 117 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 117 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 117 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel117.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell347

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell347.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 117 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell347.Kernel349

