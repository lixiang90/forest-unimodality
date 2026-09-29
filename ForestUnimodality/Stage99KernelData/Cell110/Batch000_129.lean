import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell110.Parameters
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch000_049
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch050_099
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch100_149
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch000_049
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch050_099
import ForestUnimodality.BinomialMassData.Q2294_4389.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree000.table
  base := (124785341205344673778920851/2500000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18105587265354866621791529800000000000)
      linear := (-930883692931014014582125080000000000)
      constant := (9982827296427573902313668080000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree000.table
  base := (124785341205344673778920851/2500000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18105587265354866621791529800000000000)
      linear := (-930883692931014014582125080000000000)
      constant := (9982827296427573902313668080000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree001.table
  base := (6962874578574962005238130770268986622783/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-1910609713715605876645701683046716400000000000)
      constant := (537034523358831223515483906561978117787499369372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree001.table
  base := (69568825882616201137557892120196701497823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-9562981746391484696928888793270107000000000000)
      constant := (2682869548438643556245077071571384590187490500366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12487144813449494353/25000000000000000000)
  directionHi := (49948579253797977413/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree002.table
  base := (10191246530553583903173704389888278083279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-18657799352391169920997162923512397000000000000)
      constant := (1580513333275680153336425106698490192843744876472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree002.table
  base := (162810123734458124010910545463029218660557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-37355331416036161096795847359170894000000000000)
      constant := (3156256822164240710642114382958665959437499529797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12487144813449494353/25000000000000000000)
  centralHi := (49948579253797977413/100000000000000000000)
  directionLo := (70637958201988507279/100000000000000000000)
  directionHi := (882974477524856341/1250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree003.table
  base := (12653301039735169485306707361518918221641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-3084727792911590050973979714643468000000000000)
      constant := (110785750443330497816044918337920234650542102116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree003.table
  base := (50513539881214628495766869035345377831247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-3088038852182741822207439840655643000000000000)
      constant := (110577706178706273766415075752871465003288310143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70637958201988507279/100000000000000000000)
  centralHi := (882974477524856341/1250000000000000000)
  directionLo := (43256738516729428587/50000000000000000000)
  directionHi := (3460539081338354287/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree004.table
  base := (66939162362032506561362192689510919483991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-73734601840034901993068943880140054000000000000)
      constant := (1367400573811723894412642403652936411025272994111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree004.table
  base := (66793406574968016440376254136818893190277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-73814067262542544502671986904432254000000000000)
      constant := (1364760922462967680102804883419438354389019929917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43256738516729428587/50000000000000000000)
  centralHi := (3460539081338354287/4000000000000000000)
  directionLo := (3995886340303838193/4000000000000000000)
  directionHi := (49948579253797977413/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree005.table
  base := (2936153793990700622546555249970639291571/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-45972051703830591534303126448348842000000000000)
      constant := (513070827450110813289370551210359725739958138328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree005.table
  base := (2929635166276850590808915783581173996199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-46021717592897868102805028338531467000000000000)
      constant := (512197264573983041933148458575748383965072935032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3995886340303838193/4000000000000000000)
  centralHi := (49948579253797977413/50000000000000000000)
  directionLo := (111688418591027998181/100000000000000000000)
  directionHi := (55844209295513999091/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree006.table
  base := (17306324988284790088283381157953935847003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-6119644720849303563563531217403073000000000000)
      constant := (46705152865592313251461321905416495714913964107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree006.table
  base := (4317116741549442175205936937459432987867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-6126266839391607106030451469427423000000000000)
      constant := (46645048756672603315817206778418704499231611692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111688418591027998181/100000000000000000000)
  centralHi := (55844209295513999091/50000000000000000000)
  directionLo := (122348532548770793521/100000000000000000000)
  directionHi := (61174266274385396761/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree007.table
  base := (26393404019168419732599301934946859653193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-2619655235569668269789405529179856000000000000)
      constant := (15196482655114968206292867740738833488600110897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree007.table
  base := (26336441448713898754636903681973164448439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-2622493286373512645132371351476006000000000000)
      constant := (15184539871064846889582659084485920166450375631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/100000000000000000000)
  centralHi := (61174266274385396761/50000000000000000000)
  directionLo := (66075759523274804349/50000000000000000000)
  directionHi := (132151519046549608699/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree008.table
  base := (20535313433317627720223820906595701830059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-146572608110540026295218179946370574000000000000)
      constant := (703553436103687439559767940416089373572713965939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree008.table
  base := (10245253543717696613097480280377297773697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-73365769477777655657212132997477487000000000000)
      constant := (351679294045945740225840610868070224127310667737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/50000000000000000000)
  centralHi := (132151519046549608699/100000000000000000000)
  directionLo := (141275916403977014559/100000000000000000000)
  directionHi := (882974477524856341/625000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree009.table
  base := (8049236995422628430950962553074111312459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-9154561648787017076153082720162678000000000000)
      constant := (38853579596293898182125437878245968305736557371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree009.table
  base := (16061685318270749378510097907864986598087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-18328989653200944779706926196398406000000000000)
      constant := (77722329631030149967600747278686797499960874103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141275916403977014559/100000000000000000000)
  centralHi := (882974477524856341/625000000000000000)
  directionLo := (74922868880696966119/50000000000000000000)
  directionHi := (149845737761393932239/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree010.table
  base := (12575399175513123308943588818982021351491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-182991611245792588446292797979485834000000000000)
      constant := (722284764323973777329488948634191310522624961611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree010.table
  base := (6272064855451845003336749705272048678001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-91595137401030847360150202770108167000000000000)
      constant := (361362653640215263018292751046597686011958901321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74922868880696966119/50000000000000000000)
  centralHi := (149845737761393932239/100000000000000000000)
  directionLo := (31590255266287024507/20000000000000000000)
  directionHi := (19743909541429390317/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree011.table
  base := (9681833586130595811659465360487329021043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-1662819114160486524973802537157384000000000000)
      constant := (6337510147410077336843505003532704767479066643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree011.table
  base := (965460126327984718592621445700794011409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159201000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (14412137991158800605279166678449000000000000)
      linear := (-166462514649020567291932624225493400000000000)
      constant := (634359905850476083181390114242348507410324209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/20000000000000000000)
  centralHi := (19743909541429390317/12500000000000000000)
  directionLo := (165660696196177791069/100000000000000000000)
  directionHi := (16566069619617779107/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree012.table
  base := (3625246153669755513432688606043549001141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-12189478576724730588742634222922283000000000000)
      constant := (46100214458234709895210743251494010932023161029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree012.table
  base := (7226414686048289907106169431035406375097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-24405445627618675347352949453941966000000000000)
      constant := (92315621204495898652083707648158013707659990793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165660696196177791069/100000000000000000000)
  centralHi := (16566069619617779107/10000000000000000000)
  directionLo := (173026954066917714349/100000000000000000000)
  directionHi := (3460539081338354287/2000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree013.table
  base := (1294201537513712182635498039277018264627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-118810057974335715836452362514579362000000000000)
      constant := (454582905851367798764950230618538801258745692534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree013.table
  base := (2577670864523864259515781471427120134363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-118939189285910634914557307429054187000000000000)
      constant := (455256419662233191684853212182153789253797599523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/100000000000000000000)
  centralHi := (3460539081338354287/2000000000000000000)
  directionLo := (180092163636145452033/100000000000000000000)
  directionHi := (90046081818072726017/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree014.table
  base := (3390987723579453221933575113267738586651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-5221012602373422709151878245830946000000000000)
      constant := (20481229495742859019505054817898856802831520979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree014.table
  base := (421472912017872748322749327875754871779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-2613344351990555729918904945211623000000000000)
      constant := (10257668589805347913058210804699002547950425964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180092163636145452033/100000000000000000000)
  centralHi := (90046081818072726017/50000000000000000000)
  directionLo := (93445235261918421687/50000000000000000000)
  directionHi := (1495123764190694747/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree015.table
  base := (1843455660919559545389684120056442908979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-30448791009324888202664371451363776000000000000)
      constant := (123565784358466506894676647307736066152648473251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree015.table
  base := (365251964934466003507514093992558672273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-6096380320407281182999794542297105200000000000)
      constant := (24757855501585419817722276701879946812814288737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93445235261918421687/50000000000000000000)
  centralHi := (1495123764190694747/800000000000000000)
  directionLo := (12090625976042553281/6250000000000000000)
  directionHi := (193450015616680852497/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree016.table
  base := (248534627884504779213569984832145971143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-146124310325775137449758326039415807000000000000)
      constant := (616992900079694379621754831067125870960984345903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree016.table
  base := (240842609515326778290710513523409990627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-146283241170790422468964412088000207000000000000)
      constant := (618177182635723837358657094738757919664054892267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12090625976042553281/6250000000000000000)
  centralHi := (193450015616680852497/100000000000000000000)
  directionLo := (199794317015191909651/100000000000000000000)
  directionHi := (49948579253797977413/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree017.table
  base := (-135427755851578074666766554491752437897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-62091624443835311195010792219077848800000000000)
      constant := (273740692387112163248658589013454672036257524063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree017.table
  base := (-138175586511222437158658613019759846139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-62159170052966807328173378789726218800000000000)
      constant := (274289338849864490944814438852906056340913832381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199794317015191909651/100000000000000000000)
  centralHi := (49948579253797977413/25000000000000000000)
  directionLo := (205943268112944010209/100000000000000000000)
  directionHi := (20594326811294401021/10000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree018.table
  base := (-106400695309686198549686774756787773211/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-18259312432600157613921737228441493000000000000)
      constant := (84210961851871248832235313678956905285121161128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree018.table
  base := (-342930956425874191885603755399047817551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-7311671515290827296528999193805817200000000000)
      constant := (33754068687687130357643932752178089021796183681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205943268112944010209/100000000000000000000)
  centralHi := (20594326811294401021/10000000000000000000)
  directionLo := (211913874605965521839/100000000000000000000)
  directionHi := (2648923432574569023/1250000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree019.table
  base := (-1298875740654998279806379685974530209783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2668050)
      previous := (1334025)
      next := (1334025)
      square := (24153306051665025945135445541445000000000000)
      linear := (-480439231792838113748100525108732000000000000)
      constant := (2319807867009282855126462256508149843475769337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree019.table
  base := (-521727454022550518028690646146753114243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106722000000000000000000000000000000000000000
      center := (1067220)
      previous := (533610)
      next := (533610)
      square := (9661322420666010378054178216578000000000000)
      linear := (-192384812250050094208721902212682800000000000)
      constant := (929887926601911164269845069873322307070879277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/100000000000000000000)
  centralHi := (2648923432574569023/1250000000000000000)
  directionLo := (43544161868147521651/20000000000000000000)
  directionHi := (3401887645949025129/1562500000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree020.table
  base := (-1689442682730077783633353645756567600093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-182543313461027699600832944072531067000000000000)
      constant := (922856218096057453783021430061640940461208911147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree020.table
  base := (-1694270797441964178618040507044460443317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-182741977017296805874840551633261567000000000000)
      constant := (924843898893330024938891744649337437208582324243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/20000000000000000000)
  centralHi := (3401887645949025129/1562500000000000000)
  directionLo := (223376837182055996363/100000000000000000000)
  directionHi := (55844209295513999091/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree021.table
  base := (-4058923183804105150095847208379179107369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-869152218797464127612705662498004000000000000)
      constant := (4598590095240414759133227830370760577411014711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree021.table
  base := (-813493943348569348849610227192257057131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (873620)
      previous := (436810)
      next := (436810)
      square := (7908701573379659289064758131938000000000000)
      linear := (-174019647146415783878738853986010800000000000)
      constant := (921723797954451200582394900222999819487460789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223376837182055996363/100000000000000000000)
  centralHi := (55844209295513999091/25000000000000000000)
  directionLo := (228893145286030118801/100000000000000000000)
  directionHi := (114446572643015059401/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree022.table
  base := (-4648845240089265392529642986403449397761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-3318228347581057531840830629571714000000000000)
      constant := (18359397936294728669654758050761912452427051039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree022.table
  base := (-4656393716231786562679543350023998185713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-3321840412240495827731878039766814000000000000)
      constant := (18399800652195375395940790859898837464836304687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228893145286030118801/100000000000000000000)
  centralHi := (114446572643015059401/50000000000000000000)
  directionLo := (117139801656401815113/50000000000000000000)
  directionHi := (234279603312803630227/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree023.table
  base := (-515787337638268990745795124956162213041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-41971513162493424242827781519473502400000000000)
      constant := (242606154776008373104815256717772011312120830839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree023.table
  base := (-51645272401203174554234407363953866989/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3852664200000000000000000000000000000000000000
      center := (38526642)
      previous := (19263321)
      next := (19263321)
      square := (348773739386042974647755833618465800000000000)
      linear := (-8403441156087063737169906251688303480000000000)
      constant := (48628700512591675873776946621580420301999179062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/50000000000000000000)
  centralHi := (234279603312803630227/100000000000000000000)
  directionLo := (119772485465024027179/50000000000000000000)
  directionHi := (239544970930048054359/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree024.table
  base := (-559376555424118181626832522041812006983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-4865829257695116927820168046792140600000000000)
      constant := (29350577558916813739738262212991651276425803273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree024.table
  base := (-5599620094293043483505283374881465119291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-48711269525289597617937042484116206000000000000)
      constant := (294158791959216910293197455369981197384088241621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/50000000000000000000)
  centralHi := (239544970930048054359/100000000000000000000)
  directionLo := (122348532548770793521/50000000000000000000)
  directionHi := (244697065097541587043/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree025.table
  base := (-372690924716684270890896954266529077233/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-228067067380093402289676216613925142000000000000)
      constant := (1433916300111437384758191178321944890385415433656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree025.table
  base := (-1193639454979082506446097740018377350657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-91326158730171914052874290425935306800000000000)
      constant := (574846498366094418891043111343661271195164648103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/50000000000000000000)
  centralHi := (244697065097541587043/100000000000000000000)
  directionLo := (31217862033623735883/12500000000000000000)
  directionHi := (49948579253797977413/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree026.table
  base := (-313562295477267083362856076001875774553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-47434363632781308565488974224440791400000000000)
      constant := (310479736660900814552879380696988617105323858974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree026.table
  base := (-3137877901088031468875670664236982299681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-237430080787056380983654760951153607000000000000)
      constant := (1555869613678275239527977671397230641889926699399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31217862033623735883/12500000000000000000)
  centralHi := (49948579253797977413/20000000000000000000)
  directionLo := (254688780291351626251/100000000000000000000)
  directionHi := (63672195072837906563/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree027.table
  base := (-1304595798907873455126828593930949693179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-10945625286565319260676156694688123200000000000)
      constant := (74496819905832315826801300403636897036160156949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree027.table
  base := (-652692831583059474370751004264829997907/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-5478772549970732818558306574165976600000000000)
      constant := (37331778824285040672363905649611063282209792317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254688780291351626251/100000000000000000000)
  centralHi := (63672195072837906563/25000000000000000000)
  directionLo := (259540431100376571523/100000000000000000000)
  directionHi := (64885107775094142881/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree028.table
  base := (-3361083056326333781833513390222495627459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-5211863667990465793938411839566563000000000000)
      constant := (36841181922175635087196816734579854516472670789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree028.table
  base := (-1345123964575293592030657158890822343387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (7862580)
      previous := (3931290)
      next := (3931290)
      square := (71178314160416933601582823187442000000000000)
      linear := (-2087015907839261817849737393663545200000000000)
      constant := (14769468852710600220601081713049939502966612077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259540431100376571523/100000000000000000000)
  centralHi := (64885107775094142881/25000000000000000000)
  directionLo := (66075759523274804349/25000000000000000000)
  directionHi := (264303038093099217397/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree029.table
  base := (-6872105945359740994948130528857943128647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-528972141030691928881501669294080804000000000000)
      constant := (3878970620881162207328295975303449701613128543313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree029.table
  base := (-6875122401436550270121757796900400729813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-529548265343872337076123731220199254000000000000)
      constant := (3887655135184242782040703225359349971712977911027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/25000000000000000000)
  centralHi := (264303038093099217397/100000000000000000000)
  directionLo := (67245332790980368579/25000000000000000000)
  directionHi := (268981331163921474317/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree030.table
  base := (-6975580181193148645166925325362891094993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-60797960288702023328559886478959826000000000000)
      constant := (461989743191908819511330082865148434149900927583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree030.table
  base := (-6978211615845854477967508735514800417319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-60864181474125058753229088999203326000000000000)
      constant := (463023602934372149033741511262108802145583349289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67245332790980368579/25000000000000000000)
  centralHi := (268981331163921474317/100000000000000000000)
  directionLo := (273579635726397098043/100000000000000000000)
  directionHi := (68394908931599274511/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree031.table
  base := (-439683415664211362102268135181594179367/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-282695572082972245516288143663598032000000000000)
      constant := (2223600921712911017770603851981107574998975217544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree031.table
  base := (-1407445532246321114701916063111496966597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-113201400238075744096399974153092122800000000000)
      constant := (891429332531895672203614043083061759941915711363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273579635726397098043/100000000000000000000)
  centralHi := (68394908931599274511/25000000000000000000)
  directionLo := (139050959771643673773/50000000000000000000)
  directionHi := (278101919543287347547/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree032.table
  base := (-1763036918585981882641037030306040890833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-291800322866785386054056798171876847000000000000)
      constant := (2373407487975380881284987835401389276161515927214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree032.table
  base := (-7054143707750384862232212876631630426277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-584236369113631912184937940538091294000000000000)
      constant := (4757419834124515995233751085425413712345259314083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139050959771643673773/50000000000000000000)
  centralHi := (278101919543287347547/100000000000000000000)
  directionLo := (282551832807954029119/100000000000000000000)
  directionHi := (882974477524856341/312500000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree033.table
  base := (-1757221916640833161359695051500969489283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8006743328421555891821759265805000000000000)
      linear := (-276313198944534918817103262332558000000000000)
      constant := (2321724034482693847147310589328426451408146026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree033.table
  base := (-7030623489722932273837528448318710050643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16013486656843111783643518531610000000000000)
      linear := (-553228408665642886949381093030966000000000000)
      constant := (4653810736231573107187646281315238337914175973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282551832807954029119/100000000000000000000)
  centralHi := (882974477524856341/312500000000000000)
  directionLo := (143466371314506090917/50000000000000000000)
  directionHi := (57386548525802436367/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree034.table
  base := (-1741640424009031122387485070927108504241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-310009824434411667129594107188434477000000000000)
      constant := (2688437326033223933902316894742567460561951511278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree034.table
  base := (-6968069845274286259553489522701222250623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-620695104960138295590814080083352654000000000000)
      constant := (5388859812233366062675510274535006184693906701017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143466371314506090917/50000000000000000000)
  centralHi := (57386548525802436367/20000000000000000000)
  directionLo := (72811940711190995163/25000000000000000000)
  directionHi := (291247762844763980653/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree035.table
  base := (-1373271286175698449591383283432772865189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (7862580)
      previous := (3931290)
      next := (3931290)
      square := (71178314160416933601582823187442000000000000)
      linear := (-2605016940556937205447859279156843200000000000)
      constant := (23294984619066698576142139504492076936281113619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree035.table
  base := (-3433832817556269445502543395759554317681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-6519637478401953951977062753632483000000000000)
      constant := (58367110303372924257193615516903572170644386151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72811940711190995163/25000000000000000000)
  centralHi := (291247762844763980653/100000000000000000000)
  directionLo := (4617184061217861249/1562500000000000000)
  directionHi := (295499779917943119937/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree036.table
  base := (-1682318166288029607764971045075860889229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-36468814000226438689459046244999123000000000000)
      constant := (335993633738928998063304956131474927408763628998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree036.table
  base := (-673040824026914135494544729465353611607/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-7301709342296051988852113551429044600000000000)
      constant := (67348129681963961133438694497710172155678337017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4617184061217861249/1562500000000000000)
  centralHi := (295499779917943119937/100000000000000000000)
  directionLo := (299691475522787864477/100000000000000000000)
  directionHi := (149845737761393932239/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree037.table
  base := (-204879826093428733958735482310926069467/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-337324076785851088742900070713270922000000000000)
      constant := (3199350460007815097111139573512997016815422081488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree037.table
  base := (-819642331009297349030423058218561021163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-337691604364948935349814144700622347000000000000)
      constant := (3206454098481547810699474327442853097564997350708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299691475522787864477/100000000000000000000)
  centralHi := (149845737761393932239/50000000000000000000)
  directionLo := (37978168290829168371/12500000000000000000)
  directionHi := (303825346326633346969/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree038.table
  base := (-198366049155336541518876377927296054701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2668050)
      previous := (1334025)
      next := (1334025)
      square := (24153306051665025945135445541445000000000000)
      linear := (-959636641467213931525398130807617000000000000)
      constant := (9362470993845691377272529180664020883601599024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree038.table
  base := (-6348565976170453631496766483507075087759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5336100)
      previous := (2668050)
      next := (2668050)
      square := (48306612103330051890270891082890000000000000)
      linear := (-1921364478263576350145613183307134000000000000)
      constant := (18766461846340153536964854449556450966242092001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37978168290829168371/12500000000000000000)
  centralHi := (303825346326633346969/100000000000000000000)
  directionLo := (38487965172564745083/12500000000000000000)
  directionHi := (61580744276103592133/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree039.table
  base := (-3052275207945936285455933427534188197669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-39503730928164152202048597747758728000000000000)
      constant := (396160180857954322180770863560834477891543400139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree039.table
  base := (-190790254703208237979721914668276740191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-39546774698689125228083579385917003000000000000)
      constant := (397037430113024301082689894483744004909986072336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38487965172564745083/12500000000000000000)
  centralHi := (61580744276103592133/20000000000000000000)
  directionLo := (311928777462812127199/100000000000000000000)
  directionHi := (389910971828515159/125000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree040.table
  base := (-2913585634373514626910304710561587298957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-364638329137290510356206034238107367000000000000)
      constant := (3756114380279886371481441462742341033590668343803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree040.table
  base := (-2913904670330464108644701019328436673133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-365035656249828722904221249359568367000000000000)
      constant := (3764420765749686271074705658262580399937266945307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311928777462812127199/100000000000000000000)
  centralHi := (389910971828515159/125000000000000000)
  directionLo := (31590255266287024507/10000000000000000000)
  directionHi := (315902552662870245071/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree041.table
  base := (-1379000783288697106964231683637282284727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-373743079921103650893974688746386182000000000000)
      constant := (3951866173718564187801624019695361923313380803266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree041.table
  base := (-5516554661179528402389769315901794550539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-748300680422910637511380568491767414000000000000)
      constant := (7921187905805865175092802863267957691096916519981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31590255266287024507/10000000000000000000)
  centralHi := (315902552662870245071/100000000000000000000)
  directionLo := (79956739611332345099/25000000000000000000)
  directionHi := (319826958445329380397/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree042.table
  base := (-5171406128783867808910000906401989278577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-1736271341065382274066863234715034000000000000)
      constant := (18833077276586094725975988141452202706322478063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree042.table
  base := (-5171882567574707227212527507894324712271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-1738163374934611857628840449579134000000000000)
      constant := (18874616689138870085274489922956796002243290449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79956739611332345099/25000000000000000000)
  centralHi := (319826958445329380397/100000000000000000000)
  directionLo := (323703790397739062361/100000000000000000000)
  directionHi := (161851895198869531181/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree043.table
  base := (-4793683969164343039409292023780311479599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-783905162977459863939023995525887624000000000000)
      constant := (8717187104640569048364971208939307255988499511721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree043.table
  base := (-191763812345098579991809712414799795297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7705328400000000000000000000000000000000000000
      center := (77053284)
      previous := (38526642)
      next := (38526642)
      square := (697547478772085949295511667236931600000000000)
      linear := (-31390376650776680836690268321481150960000000000)
      constant := (349455594859888475267439475084237058872459598663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323703790397739062361/100000000000000000000)
  centralHi := (161851895198869531181/50000000000000000000)
  directionLo := (327534737833006533919/100000000000000000000)
  directionHi := (2047092111456290837/625000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree044.table
  base := (-4383092796647067507143295374970608108047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-6629046814422199545574886814400374000000000000)
      constant := (75529979258538066238008447026629180218590809553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree044.table
  base := (-2191723869857215821948484041538298580791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72060689955794003026395833392245000000000000)
      linear := (-3318135471870538068678490817395287000000000000)
      constant := (37848077401677054009578742415787629327639492009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327534737833006533919/100000000000000000000)
  centralHi := (2047092111456290837/625000000000000000)
  directionLo := (331321392392355582139/100000000000000000000)
  directionHi := (16566069619617779107/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree045.table
  base := (-984962158382182895704164213630260757367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-45573564784039579227227700753277938000000000000)
      constant := (531733559699735242756059490231715478576030303154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree045.table
  base := (-1970077377093194575723540234334155161913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-45623230673106855795729602643460563000000000000)
      constant := (532902022193141690182537939852165348650251434103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331321392392355582139/100000000000000000000)
  centralHi := (16566069619617779107/5000000000000000000)
  directionLo := (67013051154616798909/20000000000000000000)
  directionHi := (167532627886541997273/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree046.table
  base := (-866033416524536406712319547919900264371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-419266833840169353582817961287780257000000000000)
      constant := (5006706674031995480057111574493295829838873127818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree046.table
  base := (-54131211710800106868341089147289727123/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-419723760019588298013035458677460407000000000000)
      constant := (5017695692922359621767657931192177826605671824544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67013051154616798909/20000000000000000000)
  centralHi := (167532627886541997273/50000000000000000000)
  directionLo := (84691936671885688601/25000000000000000000)
  directionHi := (67753549337508550881/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree047.table
  base := (-369512693050784848141001194529948775207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-428371584623982494120586615796059072000000000000)
      constant := (5232876175439561150648082420084818473268522870212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree047.table
  base := (-591265782151440170461038692729828507841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-171535377592485957545801797425510298800000000000)
      constant := (2097739349432276550199012266582592960778507800039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84691936671885688601/25000000000000000000)
  centralHi := (67753549337508550881/20000000000000000000)
  directionLo := (17121510357239812779/5000000000000000000)
  directionHi := (342430207144796255581/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree048.table
  base := (-2415881851928890360412771579851893262731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-97216963423954585479634504512075086000000000000)
      constant := (1214246509648059838443010595628666751069141712261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree048.table
  base := (-604019416475395484258343042717858750929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-48661458660315721079552614272232343000000000000)
      constant := (608452777876278775200736303288491862766265694398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17121510357239812779/5000000000000000000)
  centralHi := (342430207144796255581/100000000000000000000)
  directionLo := (173026954066917714349/50000000000000000000)
  directionHi := (346053908133835428699/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree049.table
  base := (-92179193757122054938511355288991589211/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35589157080208466800791411593721000000000000)
      linear := (-1822779943639219490596424182908639600000000000)
      constant := (23266959083068903412023741013679855201050137562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree049.table
  base := (-921876221085265542850175355752219928939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-9123832896009552766682501292579723000000000000)
      constant := (116589276093450125723653218092025147531556139869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173026954066917714349/50000000000000000000)
  centralHi := (346053908133835428699/100000000000000000000)
  directionLo := (34964005477658584189/10000000000000000000)
  directionHi := (349640054776585841891/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree050.table
  base := (-1239299782668474743954115270498366308779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-911371673950843831467785158641791034000000000000)
      constant := (11883524667019051754358308026368841839818405004941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree050.table
  base := (-1239444833647634355828886534075702495221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-912364991732189362837823196445443534000000000000)
      constant := (11909492148910432033852161732853670504534056911059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34964005477658584189/10000000000000000000)
  centralHi := (349640054776585841891/100000000000000000000)
  directionLo := (353189791009942536399/100000000000000000000)
  directionHi := (882974477524856341/250000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree051.table
  base := (-150776826616544175686938319581596201643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-51643398639915006252406803758797148000000000000)
      constant := (687575624355706891444318751827973433788971147466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree051.table
  base := (-301616036045883814796787514134351213883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-51699686647524586363375625901004123000000000000)
      constant := (689076543849434137316566951647882150826692457173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353189791009942536399/100000000000000000000)
  centralHi := (882974477524856341/250000000000000000)
  directionLo := (356704203848398489013/100000000000000000000)
  directionHi := (178352101924199244507/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree052.table
  base := (12985599386477342151478747176317210093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-189558135417219278723771955334981258800000000000)
      constant := (2575863680403651741321658180010831583615845898853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree052.table
  base := (12964144203376428987777711592156119523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-189764745515739149248739867198140978800000000000)
      constant := (2581480944768056559627105296694508462012485915883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356704203848398489013/100000000000000000000)
  centralHi := (178352101924199244507/50000000000000000000)
  directionLo := (360184327272290904067/100000000000000000000)
  directionHi := (90046081818072726017/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree053.table
  base := (764750839366187795040081817845546067529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-966000178653722674694397085691463924000000000000)
      constant := (13392395092832062359885672217210145201819098803809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree053.table
  base := (382329317777740763669513322229073440809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-483526547750974468973318702881667787000000000000)
      constant := (6710785947405257361585799194898420003222878266689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360184327272290904067/100000000000000000000)
  centralHi := (90046081818072726017/25000000000000000000)
  directionLo := (90907786445271596317/25000000000000000000)
  directionHi := (363631145781086385269/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree054.table
  base := (11689957755414293636417484662594795471/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-54678315567852719764996355261556753000000000000)
      constant := (773088356257292457336378734779342827026398003136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree054.table
  base := (187029421448929376364777229656262961223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-54737914634733451647198637529775903000000000000)
      constant := (774771022795002576733217793759733155592199645148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90907786445271596317/25000000000000000000)
  centralHi := (363631145781086385269/100000000000000000000)
  directionLo := (367045597646312380563/100000000000000000000)
  directionHi := (91761399411578095141/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree055.table
  base := (2259579932355047538878271013440966970063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-8284456047842770552441914906814704000000000000)
      constant := (119412426478465148721873060181847672882600999663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree055.table
  base := (1129755944640594929370807597052362399471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72060689955794003026395833392245000000000000)
      linear := (-4146743104745683146084766716151227000000000000)
      constant := (59836047596288593496125982084188143146358182671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367045597646312380563/100000000000000000000)
  centralHi := (91761399411578095141/25000000000000000000)
  directionLo := (92607144473648594367/25000000000000000000)
  directionHi := (370428577894594377469/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree056.table
  base := (1527256846701948303472437492091250175417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-10414578401597974672663357272868743000000000000)
      constant := (152983000283204823782409158531036049090211509793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree056.table
  base := (3054455270467450380058795533481994804943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-20851861209626704348070441124106686000000000000)
      constant := (306630746625976811069029763005306019135672436647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92607144473648594367/25000000000000000000)
  centralHi := (370428577894594377469/100000000000000000000)
  directionLo := (373780941047673686749/100000000000000000000)
  directionHi := (1495123764190694747/400000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree057.table
  base := (121283997053372743978735418077525689099/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (296450)
      previous := (148225)
      next := (148225)
      square := (2683700672407225105015049504605000000000000)
      linear := (-159870450126843305478077304056278000000000000)
      constant := (2392410148570792408654511722091786146970687536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree057.table
  base := (485129719847521121169022212425841641607/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (296450)
      previous := (148225)
      next := (148225)
      square := (2683700672407225105015049504605000000000000)
      linear := (-160044716404272346069312047530603000000000000)
      constant := (2397603427938327594390191738901737260372351612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373780941047673686749/100000000000000000000)
  centralHi := (1495123764190694747/400000000000000000)
  directionLo := (75420700728634827423/20000000000000000000)
  directionHi := (94275875910793534279/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree058.table
  base := (2369639490137979533541890897274232123679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-528523843245927040036041815387126037000000000000)
      constant := (8054772251234391405594662698868772084426940277959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree058.table
  base := (2369617975125822009646053262280749186529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-529099967559107448230663877313244487000000000000)
      constant := (8072242268837432007131651580218333699700597002809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75420700728634827423/20000000000000000000)
  centralHi := (94275875910793534279/25000000000000000000)
  directionLo := (380397046557186596959/100000000000000000000)
  directionHi := (2377481540982416231/625000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree059.table
  base := (5629067023028141086519217136494320578987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1075257188059480361147620939790809704000000000000)
      constant := (16683323715695347813240921410353342005489932435827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree059.table
  base := (2814515055422436420840059966747439065289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-538214651520734044082132912199559827000000000000)
      constant := (8359739296662304125734670111876892102642601964769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380397046557186596959/100000000000000000000)
  centralHi := (2377481540982416231/625000000000000000)
  directionLo := (38366231714738851211/10000000000000000000)
  directionHi := (383662317147388512111/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree060.table
  base := (6550435256051784156516819699179596559177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-121496298847456293580350916534151926000000000000)
      constant := (1918579829099376247305760170824933993907769116313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree060.table
  base := (6550403600994953627970926186530523282377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-121628741218302364429689321574638926000000000000)
      constant := (1922734324573245046232676512390533909587377977113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38366231714738851211/10000000000000000000)
  centralHi := (383662317147388512111/100000000000000000000)
  directionLo := (386900031233361704993/100000000000000000000)
  directionHi := (193450015616680852497/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree061.table
  base := (1875842382376672777195229223392307251661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-555838095597366461649347778911962482000000000000)
      constant := (8930614234246492115982957607478626242788747252362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree061.table
  base := (1875835597595927628582134923318754158041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-556444019443987235785070981972190507000000000000)
      constant := (8949937625454066377169011720970303715332857028322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386900031233361704993/100000000000000000000)
  centralHi := (193450015616680852497/50000000000000000000)
  directionLo := (195055437464486747233/50000000000000000000)
  directionHi := (390110874928973494467/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree062.table
  base := (265245559686921497208534144388475185399/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-564942846381179602187116433420241297000000000000)
      constant := (9232676752807003954420682078350403763150007201264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree062.table
  base := (4243917324399408184233558154578540540867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-565558703405613831636540016858505847000000000000)
      constant := (9252638677341106355247456517759172010150234639307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195055437464486747233/50000000000000000000)
  centralHi := (390110874928973494467/100000000000000000000)
  directionLo := (393295506340108262207/100000000000000000000)
  directionHi := (6145242286564191597/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree063.table
  base := (9503890333326363843983985773591530396057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-2603390463333300420521020806932064000000000000)
      constant := (43264384080246051837696328558870581139230165817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree063.table
  base := (4751935200573614290447860500031078575401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19771753933449148222661895329845000000000000)
      linear := (-1303114257068572397931993314614107000000000000)
      constant := (21678928617151956915999383065868163543252091081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393295506340108262207/100000000000000000000)
  centralHi := (6145242286564191597/1562500000000000000)
  directionLo := (198227278569824413047/50000000000000000000)
  directionHi := (79290911427929765219/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree064.table
  base := (2110291662372644018412441396311281238033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-233260939179522353305061496974719570800000000000)
      constant := (3940789585263123864907837913936307101609507087593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree064.table
  base := (5275720618281711895143783180893616920809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-583788071328867023339478086631136527000000000000)
      constant := (9873244072912185079122707518003408377596575346689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198227278569824413047/50000000000000000000)
  centralHi := (79290911427929765219/20000000000000000000)
  directionLo := (399588634030383819303/100000000000000000000)
  directionHi := (49948579253797977413/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree065.table
  base := (2907638671864009620961562572756982644733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-592257098732619023800422396945077742000000000000)
      constant := (10169208504252933710747849741218923347103841476586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree065.table
  base := (2907635015782566131332312113339197606367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-592902755290493619190947121517451867000000000000)
      constant := (10191148267278684430492876079766978520747758329614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399588634030383819303/100000000000000000000)
  centralHi := (49948579253797977413/12500000000000000000)
  directionLo := (100674580026359233199/25000000000000000000)
  directionHi := (402698320105436932797/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree066.table
  base := (2548234684651667001685033602180419704093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35378000000000000000000000000000000000000000
      center := (353780)
      previous := (176890)
      next := (176890)
      square := (3202697331368622356728703706322000000000000)
      linear := (-220885895139185367984643177760645200000000000)
      constant := (3853627274503129752446293029374272644145701077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree066.table
  base := (12741160901060347688169273738265646910769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16013486656843111783643518531610000000000000)
      linear := (-1105633497249072938553565025534926000000000000)
      constant := (19309678688095920891186556018690557028204592841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100674580026359233199/25000000000000000000)
  centralHi := (402698320105436932797/100000000000000000000)
  directionLo := (202892088057428873913/50000000000000000000)
  directionHi := (405784176114857747827/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree067.table
  base := (13883309428079662254754127242166315894557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1220933200600490609751919411923270744000000000000)
      constant := (21637698331733405705649712195671698883964253643797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree067.table
  base := (13883298708307153293672601393338869318827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1222264246427493621787770382580165094000000000000)
      constant := (21684318719035076515388065550742072449465615844467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202892088057428873913/50000000000000000000)
  centralHi := (405784176114857747827/100000000000000000000)
  directionLo := (10221168541154150579/2500000000000000000)
  directionHi := (408846741646166023161/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree068.table
  base := (15056958408261999576008916317846410939667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1239142702168116890827456720939828374000000000000)
      constant := (22302510391987347316290237014711331134628717054107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree068.table
  base := (15056949233520932564327705487528213160009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1240493614350746813490708452352795774000000000000)
      constant := (22350532335758109961672908193488518378657677729889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10221168541154150579/2500000000000000000)
  centralHi := (408846741646166023161/100000000000000000000)
  directionLo := (411886536225888020419/100000000000000000000)
  directionHi := (20594326811294401021/5000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree069.table
  base := (8131058371378560846932320874480014851861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-69852900207541287327944112775354778000000000000)
      constant := (1276524256704330667443052957582929680658462876709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree069.table
  base := (16262108892061620515117201014176329724047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-139858109141555556132627391347269606000000000000)
      constant := (2558542319161498438676604150514391860675128753343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411886536225888020419/100000000000000000000)
  centralHi := (20594326811294401021/5000000000000000000)
  directionLo := (2593150377177831049/625000000000000000)
  directionHi := (414904060348452967841/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree070.table
  base := (1749878137777094447790907525370132223457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35589157080208466800791411593721000000000000)
      linear := (-2603187153680345822405165997903966600000000000)
      constant := (48290769304038783853466784174077966710875426953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree070.table
  base := (17498774661453379197165926537706355006433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-26060252044841901977481318202001166000000000000)
      constant := (483946209610169024356826310418464481637323998857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2593150377177831049/625000000000000000)
  centralHi := (414904060348452967841/100000000000000000000)
  directionLo := (417899796438219912167/100000000000000000000)
  directionHi := (52237474554777489021/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree071.table
  base := (18766949737910043423116325764329908053127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1293771206870995734054068647989501264000000000000)
      constant := (24357631357279873301431970188178823750227870454767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree071.table
  base := (2345867999154034735381165007566886965717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-647590859060253194299761330835343907000000000000)
      constant := (12204991241000309971666960460035185332365290264628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417899796438219912167/100000000000000000000)
  centralHi := (52237474554777489021/12500000000000000000)
  directionLo := (84174841949974239961/20000000000000000000)
  directionHi := (210437104874935599903/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree072.table
  base := (2508327456405697937254518684611724323117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-72887817135479000840533664278114383000000000000)
      constant := (1392383320763444295294878884622822563110982440692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree072.table
  base := (20066614738616625807516926032546591384231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-145934565115973286700273414604813166000000000000)
      constant := (2790748384929758636611553034740916067254475121239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84174841949974239961/20000000000000000000)
  centralHi := (210437104874935599903/50000000000000000000)
  directionLo := (211913874605965521839/50000000000000000000)
  directionHi := (423827749211931043679/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree073.table
  base := (4279557857222950544302341550746823580221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-266038042001249659241028653204523304800000000000)
      constant := (5155656434616293483774120663274345092256166373941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree073.table
  base := (10698892542916264908686066496662685312171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-665820226983506386002699400607974587000000000000)
      constant := (12916811591549561734382464942812059701890335179891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211913874605965521839/50000000000000000000)
  centralHi := (423827749211931043679/100000000000000000000)
  directionLo := (426760848217739455193/100000000000000000000)
  directionHi := (213380424108869727597/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree074.table
  base := (4552091419564246601379863805380917510199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-269679942314774915456136115007834830800000000000)
      constant := (5300755705108460517859839463399289804473484110879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree074.table
  base := (22760453507267106100456520338950151030731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1349869821890265963708336870988579854000000000000)
      constant := (26560645608767609816507467279991645538303452117651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426760848217739455193/100000000000000000000)
  centralHi := (213380424108869727597/50000000000000000000)
  directionLo := (214836962683913746749/50000000000000000000)
  directionHi := (429673925367827493499/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree075.table
  base := (603865544592105070531290011776396917743/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-15184546812683342870624643156174797600000000000)
      constant := (302659875622561600009563604595670953327730668668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree075.table
  base := (603865467872708547268427790155818408757/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-15201102109039101726791943786235672600000000000)
      constant := (303308919072909976877371093039722045566931245332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214836962683913746749/50000000000000000000)
  centralHi := (429673925367827493499/100000000000000000000)
  directionLo := (27035461572955892867/6250000000000000000)
  directionHi := (432567385167294285873/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree076.table
  base := (25580282245128223669499944244527275529979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5336100)
      previous := (2668050)
      next := (2668050)
      square := (48306612103330051890270891082890000000000000)
      linear := (-3836062921631931134159986684410774000000000000)
      constant := (77521088624332355509997011347192543949555209419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree076.table
  base := (12790139811386117822345255270982313094103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2668050)
      previous := (1334025)
      next := (1334025)
      square := (24153306051665025945135445541445000000000000)
      linear := (-1920122656145114054174810263897287000000000000)
      constant := (38843621171138960323456144755316319209014430183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27035461572955892867/6250000000000000000)
  centralHi := (432567385167294285873/100000000000000000000)
  directionLo := (43544161868147521651/10000000000000000000)
  directionHi := (435441618681475216511/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree077.table
  base := (2703743755571118092290959467329448618727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3249000000000000000000000000000000000000000
      center := (32490)
      previous := (16245)
      next := (16245)
      square := (294125265125689808271003401601000000000000)
      linear := (-23663825540171250135053002227843600000000000)
      constant := (484752084158479672154354426425527328562244023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree077.table
  base := (27037435315221588388742543608808322811677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32490000000000000000000000000000000000000000
      center := (324900)
      previous := (162450)
      next := (162450)
      square := (2941252651256898082710034016010000000000000)
      linear := (-236896260020243808199890551578086000000000000)
      constant := (4857905363152418761486667545475190240815138573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43544161868147521651/10000000000000000000)
  centralHi := (435441618681475216511/100000000000000000000)
  directionLo := (219148502076455113051/50000000000000000000)
  directionHi := (438297004152910226103/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree078.table
  base := (14263043467080093564814910026117811669121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-78957650991354427865712767283633593000000000000)
      constant := (1639272390005415102780395014666042578444424845649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree078.table
  base := (28526085020252615703389559938129885467313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-158087477064808747835565461119900286000000000000)
      constant := (3285564659932847295159227441952513452827787258497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219148502076455113051/50000000000000000000)
  centralHi := (438297004152910226103/100000000000000000000)
  directionLo := (441133907582367943393/100000000000000000000)
  directionHi := (220566953791183971697/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree079.table
  base := (15023114860815518760919186398833958209647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-719723609706002991329183560060981152000000000000)
      constant := (15141484415858044598861469816924153049443015457687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree079.table
  base := (30046228086970408542277294759316336240023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1441016661506531922223027219851733254000000000000)
      constant := (30347777596818736242045395732693727721535496096383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441133907582367943393/100000000000000000000)
  centralHi := (220566953791183971697/50000000000000000000)
  directionLo := (221976341638226211789/50000000000000000000)
  directionHi := (443952683276452423579/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree080.table
  base := (1579893268126483538666438577662338256933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-145765672097963226373390442913851993400000000000)
      constant := (3106914849390952505603876088970035294907761708986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree080.table
  base := (6319572793319283141605300972568692696071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-291849205885957022785193057924872786800000000000)
      constant := (6227121571965745040812289484360717545954771111791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221976341638226211789/50000000000000000000)
  centralHi := (443952683276452423579/100000000000000000000)
  directionLo := (446753674364111992727/100000000000000000000)
  directionHi := (55844209295513999091/12500000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree081.table
  base := (1327239735533508287947278405179982106027/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77505275419120661032834629692992400000000000)
      linear := (-6559405433543371310264185502911455840000000000)
      constant := (141624186656233597700953189922889151660294903963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree081.table
  base := (8295248049113528232020734354635274688479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-82081966519613239201605742188721923000000000000)
      constant := (1774087373306272563125260999039970814499410217502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446753674364111992727/100000000000000000000)
  centralHi := (55844209295513999091/12500000000000000000)
  directionLo := (112384303321045449179/25000000000000000000)
  directionHi := (449537213284181796717/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree082.table
  base := (8698903350992881438201093555824281655407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-747037862057442412942489523585817597000000000000)
      constant := (16335924667667284931858033679246053228245032853294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree082.table
  base := (17397806193232933117792378381729452355543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-747852382638145748665920714584812647000000000000)
      constant := (16370836084178544180300492256208364179879030938303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112384303321045449179/25000000000000000000)
  centralHi := (449537213284181796717/100000000000000000000)
  directionLo := (226151811122960549991/50000000000000000000)
  directionHi := (452303622245921099983/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree083.table
  base := (36441725076278042499263209146970021999473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1512285225682511106960516356188192824000000000000)
      constant := (33488370500537921401036111055597613300652910229833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree083.table
  base := (36441724207767223007559868766742316814061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1513934133199544689034779498942255974000000000000)
      constant := (33559906200026250360734703587610481345072954356581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226151811122960549991/50000000000000000000)
  centralHi := (452303622245921099983/100000000000000000000)
  directionLo := (227526606832175690423/50000000000000000000)
  directionHi := (455053213664351380847/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree084.table
  base := (38119328124332510606875426829011192226603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-3470509585601218566975178379149094000000000000)
      constant := (77811803827326690520684324607346753887650245643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree084.table
  base := (38119327383106607731413822669688620709747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-3474293653339677734099132808877294000000000000)
      constant := (77977947413105682629934260227930044641222458707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227526606832175690423/50000000000000000000)
  centralHi := (455053213664351380847/100000000000000000000)
  directionLo := (457786290572060237603/100000000000000000000)
  directionHi := (114446572643015059401/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree085.table
  base := (3982842231125608353937121790095937986861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-154870422881776366911159097422130808400000000000)
      constant := (3515175429271094396053519216674554546986997225381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree085.table
  base := (19914210839375230873091118455320867522739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-775196434523025536220327819243758667000000000000)
      constant := (17613388995657335414420706489774035499088996156219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457786290572060237603/100000000000000000000)
  centralHi := (114446572643015059401/25000000000000000000)
  directionLo := (460503147009007643871/100000000000000000000)
  directionHi := (14390723344031488871/3125000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree086.table
  base := (41569007437315093846707446363582422999347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1566913730385389950187128283237865714000000000000)
      constant := (35998616911270007973178893707714629428194204051387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree086.table
  base := (8313801379531552983970474577928726176849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-313724447393860852828718741652029602800000000000)
      constant := (7215083148527156061377098496992632636265745055529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460503147009007643871/100000000000000000000)
  centralHi := (14390723344031488871/3125000000000000000)
  directionLo := (463204068391753920499/100000000000000000000)
  directionHi := (926408136783507841/200000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree087.table
  base := (21670541667050642961515371267225012619419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-88062401775167568403481421791912408000000000000)
      constant := (2047532963349120015042627157534602637785213225611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree087.table
  base := (43341082873724892523072024923528455643351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-176316844988061939538503530892530966000000000000)
      constant := (4103798673327025225723133068514397569076903536519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463204068391753920499/100000000000000000000)
  centralHi := (926408136783507841/200000000000000000)
  directionLo := (465889331863421810557/100000000000000000000)
  directionHi := (232944665931710905279/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree088.table
  base := (22572324929811843450519060545382238441399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72060689955794003026395833392245000000000000)
      linear := (-6625341874052241786521499592028847000000000000)
      constant := (155878857756273484148162106363383713742109162199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree088.table
  base := (4514464946693297177465194074192240958757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 159201000000000000000000000000000000000000000
      center := (1592010)
      previous := (796005)
      next := (796005)
      square := (14412137991158800605279166678449000000000000)
      linear := (-1326513200674223675660718882483809400000000000)
      constant := (31242227223586597115923402517614154152875073157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465889331863421810557/100000000000000000000)
  centralHi := (232944665931710905279/50000000000000000000)
  directionLo := (117139801656401815113/25000000000000000000)
  directionHi := (468559206625607260453/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree089.table
  base := (1879188275766772810160579172857378478053/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7705328400000000000000000000000000000000000000
      center := (77053284)
      previous := (38526642)
      next := (38526642)
      square := (697547478772085949295511667236931600000000000)
      linear := (-64861689403530751736549608411501544160000000000)
      constant := (1543995504766640286309725532863637635381226394013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree089.table
  base := (9395941311851243951283278109400883062499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-324662068147812767850481583515608010800000000000)
      constant := (7736427276430375640106742991301823175316381299179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117139801656401815113/25000000000000000000)
  centralHi := (468559206625607260453/100000000000000000000)
  directionLo := (471213954253364038209/100000000000000000000)
  directionHi := (47121395425336403821/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree090.table
  base := (976925086736246662918423000108358861943/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428073800000000000000000000000000000000000000
      center := (4280738)
      previous := (2140369)
      next := (2140369)
      square := (38752637709560330516417314846496200000000000)
      linear := (-3643892748124211276642838931786880520000000000)
      constant := (87749345477296589226781425256639962748978076967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree090.table
  base := (2442312702560596750572681260020861522181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2140369000000000000000000000000000000000000000
      center := (21403690)
      previous := (10701845)
      next := (10701845)
      square := (193763188547801652582086574232481000000000000)
      linear := (-18239330096247967010614955415007452600000000000)
      constant := (439681248698479409891063696165487746710738049578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471213954253364038209/100000000000000000000)
  centralHi := (47121395425336403821/10000000000000000000)
  directionLo := (94770765798861073521/20000000000000000000)
  directionHi := (236926914497152683803/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree091.table
  base := (792879564101093308458229836503240002779/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-16917971818607360771069539064496468000000000000)
      constant := (412088133798281436204947369236845438399680175712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree091.table
  base := (6343036482368940776299416841028200621961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-16936419148832349210798816909421443000000000000)
      constant := (412965540214881492337529914889918919929243623876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94770765798861073521/20000000000000000000)
  centralHi := (236926914497152683803/50000000000000000000)
  directionLo := (476479078052790615899/100000000000000000000)
  directionHi := (4764790780527906159/1000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree092.table
  base := (26336910059709873643029938465579899677693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-838085369895573818320176068668605747000000000000)
      constant := (20646091280064370311026124653104852092639196798453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree092.table
  base := (26336909955903869197359658938821470781511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-838999222254411707180611063447966047000000000000)
      constant := (20690034027688155130362728560552278177356367258031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476479078052790615899/100000000000000000000)
  centralHi := (4764790780527906159/1000000000000000000)
  directionLo := (119772485465024027179/25000000000000000000)
  directionHi := (479089941860096108717/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree093.table
  base := (27317419163602776287146660759329208195251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-94132235631042995428660524797431618000000000000)
      constant := (2344991211517242187468755432621335335765661187619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree093.table
  base := (10926967630045308106597018518015287260249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-37693951387379480134759115481523617200000000000)
      constant := (939992171659326900189682443161821995977931891881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119772485465024027179/25000000000000000000)
  centralHi := (479089941860096108717/100000000000000000000)
  directionLo := (96337330866281157813/20000000000000000000)
  directionHi := (240843327165702894533/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree094.table
  base := (56627346674871803721097984479535770394181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1712589742926400198791426755370326754000000000000)
      constant := (43137614852794863236123072105872345172085405135101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree094.table
  base := (11325469304804671073542086839161597845443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-342891436071065959553419653288238690800000000000)
      constant := (8645872389594373074309702075427491161369676896203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96337330866281157813/20000000000000000000)
  centralHi := (240843327165702894533/50000000000000000000)
  directionLo := (242134721555199588607/50000000000000000000)
  directionHi := (96853888622079835443/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree095.table
  base := (58651345119474225122212716135445545038517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5336100)
      previous := (2668050)
      next := (2668050)
      square := (48306612103330051890270891082890000000000000)
      linear := (-4794457740980682769714581895808544000000000000)
      constant := (122092802481315797343577065839865927228800305637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree095.table
  base := (29325672495456385437140214780175758539627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2668050)
      previous := (1334025)
      next := (1334025)
      square := (24153306051665025945135445541445000000000000)
      linear := (-2399842864651776993725812100019147000000000000)
      constant := (61176192139152655656947979851210848651433036347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242134721555199588607/50000000000000000000)
  centralHi := (96853888622079835443/20000000000000000000)
  directionLo := (486838529802160464581/100000000000000000000)
  directionHi := (243419264901080232291/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree096.table
  base := (2428273344992957748358574236164756749123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 856147600000000000000000000000000000000000000
      center := (8561476)
      previous := (4280738)
      next := (4280738)
      square := (77505275419120661032834629692992400000000000)
      linear := (-7773372204718456715300006104015297840000000000)
      constant := (200104454824416268047165500612271148878363646387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree096.table
  base := (12141366703053769579605409867936034961481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-38909242582263026248288320133032329200000000000)
      constant := (1002648756743833169888370317131131378414470126489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486838529802160464581/100000000000000000000)
  centralHi := (243419264901080232291/50000000000000000000)
  directionLo := (122348532548770793521/25000000000000000000)
  directionHi := (97878826039016634817/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree097.table
  base := (1962306630013385819333369167081567069407/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-883609123814639521009019341209999822000000000000)
      constant := (22990808385711723323728931247770564342006261130352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree097.table
  base := (7849226508384982904348694201895877343319/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-884572642062544686437956237879542747000000000000)
      constant := (23039655967203282847842140981733734509363924409596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122348532548770793521/25000000000000000000)
  centralHi := (97878826039016634817/20000000000000000000)
  directionLo := (491936454472399268509/100000000000000000000)
  directionHi := (49193645447239926851/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree098.table
  base := (6491228070059787765128213614924227232231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393129000000000000000000000000000000000000000
      center := (3931290)
      previous := (1965645)
      next := (1965645)
      square := (35589157080208466800791411593721000000000000)
      linear := (-3643730100401847598150155084564402600000000000)
      constant := (95816010210305093280112758089730425327579740799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree098.table
  base := (64912280621066997662425075512675036492971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-36477033715272297236303072357790126000000000000)
      constant := (960195191158846582189024207710553792421445196259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491936454472399268509/100000000000000000000)
  centralHi := (49193645447239926851/10000000000000000000)
  directionLo := (247232853706959775479/50000000000000000000)
  directionHi := (494465707413919550959/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree099.table
  base := (67062239223692786896358938456844556650077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (1768900)
      previous := (884450)
      next := (884450)
      square := (16013486656843111783643518531610000000000000)
      linear := (-1656232553502783842212225252941336000000000000)
      constant := (44011191028425118473832627026980104862583212053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree099.table
  base := (33531119577970629778691406852180438426933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88445000000000000000000000000000000000000000
      center := (884450)
      previous := (442225)
      next := (442225)
      square := (8006743328421555891821759265805000000000000)
      linear := (-829019292916251495078874479019443000000000000)
      constant := (22052319260878395987281729416053461775334017837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247232853706959775479/50000000000000000000)
  centralHi := (494465707413919550959/100000000000000000000)
  directionLo := (496982088588533373209/100000000000000000000)
  directionHi := (49698208858853337321/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree100.table
  base := (69243687711487897132202834231385683244911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1821846752332157885244650609469672534000000000000)
      constant := (48916642851788744148305222615311890591151042209431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree100.table
  base := (3462184382688848307860510722332900156103/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-182383338789484894798472668507697753400000000000)
      constant := (4902047288429024931359925314447730689135924396126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496982088588533373209/100000000000000000000)
  centralHi := (49698208858853337321/10000000000000000000)
  directionLo := (499485792537979774129/100000000000000000000)
  directionHi := (49948579253797977413/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree101.table
  base := (35728313074318456232959499165692858778067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-920028126949892083160093959243115082000000000000)
      constant := (24957606234127622737106956088410189601799572380507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree101.table
  base := (71456626099483503811698805693091034858161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1842062755818102139687664754849608214000000000000)
      constant := (50021128968784095752330178092804955090694944812681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499485792537979774129/100000000000000000000)
  centralHi := (49948579253797977413/10000000000000000000)
  directionLo := (62747126119046120263/12500000000000000000)
  directionHi := (100395401790473792421/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree102.table
  base := (36850527261110334145418154584199982882713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-103236986414856135966429179305710433000000000000)
      constant := (2829105326616977332269980831128808889162689541097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree102.table
  base := (73701054480359954824409832697941895796661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-206699124860150592376733647180248766000000000000)
      constant := (5670213289270002657990144580404482629564403507909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62747126119046120263/12500000000000000000)
  centralHi := (100395401790473792421/20000000000000000000)
  directionLo := (252227961418951153743/50000000000000000000)
  directionHi := (504455922837902307487/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree103.table
  base := (37988486410683087616306611362250417105313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-938237628517518364235631268259672712000000000000)
      constant := (25971346542065166891847460319876732001833535124473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree103.table
  base := (37988486392859797651047529392181330502121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-939260745832304261546770447197434787000000000000)
      constant := (26026422394011086014774306010596688885669448003841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252227961418951153743/50000000000000000000)
  centralHi := (504455922837902307487/100000000000000000000)
  directionLo := (253461357338605259309/50000000000000000000)
  directionHi := (506922714677210518619/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree104.table
  base := (78284381036925366387551360642295241997379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1894684758602663009546799845535903054000000000000)
      constant := (52971604083153248733424291265647175559368192835659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree104.table
  base := (15656876201314661255227469969843675138657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 38526642000000000000000000000000000000000000000
      center := (385266420)
      previous := (192633210)
      next := (192633210)
      square := (3487737393860429746477558336184658000000000000)
      linear := (-379350171917572342959295792833500050800000000000)
      constant := (10616780904477475958208489941027064333215669299897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253461357338605259309/50000000000000000000)
  centralHi := (506922714677210518619/100000000000000000000)
  directionLo := (509377560582703252503/100000000000000000000)
  directionHi := (63672195072837906563/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree105.table
  base := (40311639580602097373965302567045810090119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19771753933449148222661895329845000000000000)
      linear := (-2168814353934568356714667975683062000000000000)
      constant := (61236540675766580422617873844555081780546488039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree105.table
  base := (80623279135362658661171702131593004595767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (4368100)
      previous := (2184050)
      next := (2184050)
      square := (39543507866898296445323790659690000000000000)
      linear := (-4342358792542210672334278988526374000000000000)
      constant := (122732650354603280636430140149327534033747698327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509377560582703252503/100000000000000000000)
  centralHi := (63672195072837906563/12500000000000000000)
  directionLo := (511820632443298889703/100000000000000000000)
  directionHi := (63977579055412361213/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree106.table
  base := (82993667187734192795591870363443616539149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1931103761737915571697874463569018314000000000000)
      constant := (55059767462624355215488569235970664134794536253829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree106.table
  base := (82993667165734881477343274461318323506393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1933209595434368098202355103712761614000000000000)
      constant := (55176427639877797471793909984482774172885493911153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511820632443298889703/100000000000000000000)
  centralHi := (63977579055412361213/12500000000000000000)
  directionLo := (25712604903244021461/5000000000000000000)
  directionHi := (514252098064880429221/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree107.table
  base := (85395545111079841847042049891502393809703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1949313263305541852773411772585575944000000000000)
      constant := (56119019842843236440441479670247709549724721803663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree107.table
  base := (85395545092353144433330599914868382361203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1951438963357621289905293173485392294000000000000)
      constant := (56237891022777826849402855309484553830174591335163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25712604903244021461/5000000000000000000)
  centralHi := (514252098064880429221/100000000000000000000)
  directionLo := (5166721213048022929/1000000000000000000)
  directionHi := (516672121304802292901/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree108.table
  base := (87828912926676140795831718496136561458303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-218613640541463125983216564622459286000000000000)
      constant := (6354265112954981169547645065045478343911946533807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree108.table
  base := (87828912910736616071656855444580625330459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-218852036808986053512025693695335886000000000000)
      constant := (6367720994999313244308917098714606596457929199371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5166721213048022929/1000000000000000000)
  centralHi := (516672121304802292901/100000000000000000000)
  directionLo := (519080862200753143047/100000000000000000000)
  directionHi := (64885107775094142881/12500000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree109.table
  base := (45146885315345821367778342963057721758659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-992866133220397207462243195309345602000000000000)
      constant := (29133932991902665540149013054450461807515732846539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree109.table
  base := (90293770617125627254285684366719489003643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-1987897699204127673311169313030653654000000000000)
      constant := (58391221436453350806466318072854197149633145278403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519080862200753143047/100000000000000000000)
  centralHi := (64885107775094142881/12500000000000000000)
  directionLo := (521478477094261495119/100000000000000000000)
  directionHi := (6518480963678268689/1250000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree110.table
  base := (92790118219912969126009562295527142478949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-16561502214945625586777055368886354000000000000)
      constant := (490557518548866427778798470105604056609791159749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree110.table
  base := (46395059104184001071654996005293386874519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 796005000000000000000000000000000000000000000
      center := (7960050)
      previous := (3980025)
      next := (3980025)
      square := (72060689955794003026395833392245000000000000)
      linear := (-8289781269121408533116146209930927000000000000)
      constant := (245797886227668183047301650950139332483810299319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521478477094261495119/100000000000000000000)
  centralHi := (6518480963678268689/1250000000000000000)
  directionLo := (130966279687278460863/25000000000000000000)
  directionHi := (523865118749113843453/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree111.table
  base := (744671528840995595685033097208948734569/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-112341737198669276504197833813989248000000000000)
      constant := (3358731516575860029883236207015151001969885821504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree111.table
  base := (19063591136364647273081676191658914332423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4280738000000000000000000000000000000000000000
      center := (42807380)
      previous := (21403690)
      next := (21403690)
      square := (387526377095603305164173148464962000000000000)
      linear := (-44985698556680756815934343390575889200000000000)
      constant := (1346335334374888950852824541000903942010773884087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130966279687278460863/25000000000000000000)
  centralHi := (523865118749113843453/100000000000000000000)
  directionLo := (131560234116234778733/25000000000000000000)
  directionHi := (526240936464939114933/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree112.table
  base := (19575456608728191172130482661590383026109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 786258000000000000000000000000000000000000000
      center := (7862580)
      previous := (3931290)
      next := (3931290)
      square := (71178314160416933601582823187442000000000000)
      linear := (-8328003147525196972045299255789241200000000000)
      constant := (251293831206611584428411726019040036088671205061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree112.table
  base := (97877283035281722747583819012077248094177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3931290000000000000000000000000000000000000000
      center := (39312900)
      previous := (19656450)
      next := (19656450)
      square := (355891570802084668007914115937210000000000000)
      linear := (-41685424550487494865713949435684606000000000000)
      constant := (1259127064810891712387740574589840388466015709833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131560234116234778733/25000000000000000000)
  centralHi := (526240936464939114933/100000000000000000000)
  directionLo := (66075759523274804349/12500000000000000000)
  directionHi := (528606076186198434793/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree113.table
  base := (50234050137004408289562512868702132713333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1029285136355649769613317813342460862000000000000)
      constant := (31343461893069802451002834344540634415591534558893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree113.table
  base := (50234050133448332029867154550886077259513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1030407585448570220061460796060588187000000000000)
      constant := (31409748426825599102724092663607310386680799222673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66075759523274804349/12500000000000000000)
  centralHi := (528606076186198434793/100000000000000000000)
  directionLo := (530960680606805348869/100000000000000000000)
  directionHi := (53096068060680534887/10000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree114.table
  base := (51545203690588663713476874470227177185603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (296450)
      previous := (148225)
      next := (148225)
      square := (2683700672407225105015049504605000000000000)
      linear := (-319602920018301911403843172622573000000000000)
      constant := (9821017654646732252170558732758938933533440187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree114.table
  base := (644315046094541765000762057868402251427/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5929000000000000000000000000000000000000000
      center := (59290)
      previous := (29645)
      next := (29645)
      square := (536740134481445021003009900921000000000000)
      linear := (-63990290514631998517262531914244600000000000)
      constant := (1968356481397132152244392484248294511179370928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530960680606805348869/100000000000000000000)
  centralHi := (53096068060680534887/10000000000000000000)
  directionLo := (133326222317647180883/25000000000000000000)
  directionHi := (533304889270588723533/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree115.table
  base := (26436051090958655315044660629776006960833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1047494637923276050688855122359018492000000000000)
      constant := (32478567723429575542426642600398125859119521012786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree115.table
  base := (6609012772417965438030734709296523953933/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1048636953371823411764398865833218867000000000000)
      constant := (32547220928266914847105351483749664930870404731944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133326222317647180883/25000000000000000000)
  centralHi := (533304889270588723533/100000000000000000000)
  directionLo := (535638838667798469719/100000000000000000000)
  directionHi := (13390970966694961743/2500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree116.table
  base := (27107372805222295607539236153357922668019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1056599388707089191226623776867297307000000000000)
      constant := (33053705983506316708218161809516520846494452862198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree116.table
  base := (54214745608255452745665279675624561137613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1057751637333450007615867900719534207000000000000)
      constant := (33123558090726821086359147580468685628677964392773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535638838667798469719/100000000000000000000)
  centralHi := (13390970966694961743/2500000000000000000)
  directionLo := (537962662327842948633/100000000000000000000)
  directionHi := (268981331163921474317/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree117.table
  base := (111146267951434887973514430307486132569859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-236823142109089407058753873639016916000000000000)
      constant := (7474200253370828692427161884721754325582416537971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree117.table
  base := (13893283493463865671258091423755989847013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-118540702366119622607481881733983283000000000000)
      constant := (3744995836407510622642211073575730222931445471188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537962662327842948633/100000000000000000000)
  centralHi := (268981331163921474317/50000000000000000000)
  directionLo := (540276490908436356101/100000000000000000000)
  directionHi := (270138245454218178051/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree118.table
  base := (113894534554721541296574945792130854109547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2149617780549430944604322171767709874000000000000)
      constant := (68438306386819174253280594910313724308716373025587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree118.table
  base := (113894534551554339987843806017834080193033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2151962010513406398637611940984329774000000000000)
      constant := (68582868478164353574077808092865770723498136642593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540276490908436356101/100000000000000000000)
  centralHi := (270138245454218178051/50000000000000000000)
  directionLo := (542580452281324497649/100000000000000000000)
  directionHi := (10851609045626489953/2000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree119.table
  base := (29168572757532509322639291799299624308777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1965645000000000000000000000000000000000000000
      center := (19656450)
      previous := (9828225)
      next := (9828225)
      square := (177945785401042334003957057968605000000000000)
      linear := (-22120686552214869649794484497798648000000000000)
      constant := (710397186596386280207158601040518894759770386466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree119.table
  base := (72921431892147844119421838548794676183/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 78625800000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (7117831416041693360158282318744200000000000)
      linear := (-885792399361901873608387759492636920000000000)
      constant := (28475896510175299058124760267852880152100691424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542580452281324497649/100000000000000000000)
  centralHi := (10851609045626489953/2000000000000000000)
  directionLo := (272437335807374054189/50000000000000000000)
  directionHi := (544874671614748108379/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree120.table
  base := (3733923043035982272618996273659449864367/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-121446487982482417041966488322268063000000000000)
      constant := (3933869776622649884225843762223280908747925302768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree120.table
  base := (119485537374860969439496388946070273018839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-243157860706656975782609786725510126000000000000)
      constant := (7884350996735668070388670701255015004191059411591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272437335807374054189/50000000000000000000)
  centralHi := (544874671614748108379/100000000000000000000)
  directionLo := (547159271452794196087/100000000000000000000)
  directionHi := (68394908931599274511/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree121.table
  base := (122328273595369309533802090290088174746797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-18216911448366196593644083461300684000000000000)
      constant := (595128111281790744014569523078391979007864829197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree121.table
  base := (122328273593421700973209868074544273326837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1592010000000000000000000000000000000000000000
      center := (15920100)
      previous := (7960050)
      next := (7960050)
      square := (144121379911588006052791666784490000000000000)
      linear := (-18236777803993107221044844217373734000000000000)
      constant := (596384347439926648767703584858782926857905777237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547159271452794196087/100000000000000000000)
  centralHi := (68394908931599274511/12500000000000000000)
  directionLo := (274717185895888875771/50000000000000000000)
  directionHi := (549434371791777751543/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree122.table
  base := (31300624921111228648726571843306447386943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1111227893409968034453235703916970197000000000000)
      constant := (36610730372053138139597942509131432888768588435406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree122.table
  base := (31300624920697238162062435674133539973099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1112439741103209582724682110037426247000000000000)
      constant := (36687993829376732697475069179893171238736274803558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274717185895888875771/50000000000000000000)
  centralHi := (549434371791777751543/100000000000000000000)
  directionLo := (137925022538447134633/25000000000000000000)
  directionHi := (551700090153788538533/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree123.table
  base := (128108215644104640459785914123276720855789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-248962809820840261109112079650055336000000000000)
      constant := (8271392646247912898697567746050384577241384246141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree123.table
  base := (64054107821348373401238259543506410332941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-124617158340537353175127904991526843000000000000)
      constant := (4144422434787939539032634859584070945977906595229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137925022538447134633/25000000000000000000)
  centralHi := (551700090153788538533/100000000000000000000)
  directionLo := (553956541657530513213/100000000000000000000)
  directionHi := (276978270828765256607/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree124.table
  base := (65522710737064739908680056203273535050601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1129437394977594315528773012933527827000000000000)
      constant := (37836860340733640322437444476936204614484478305921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree124.table
  base := (131045421472932572156816669965462983547789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2261338218052925548855240359620113854000000000000)
      constant := (75833354542515369750819087167486676541698778347269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553956541657530513213/100000000000000000000)
  centralHi := (276978270828765256607/50000000000000000000)
  directionLo := (556203839086574695093/100000000000000000000)
  directionHi := (278101919543287347547/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree125.table
  base := (134014117174346143964084670548984139245387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2277084291522814912133083334883613284000000000000)
      constant := (76915021339811131833064176749350485385692587550227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree125.table
  base := (134014117173328670254376506234331210614127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2279567585976178740558178429392744534000000000000)
      constant := (77077239807747607954639509648746168830378535535767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556203839086574695093/100000000000000000000)
  centralHi := (278101919543287347547/50000000000000000000)
  directionLo := (139610523238784997727/25000000000000000000)
  directionHi := (558442092955139990909/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree126.table
  base := (68507151372309792061381026585260463478203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19771753933449148222661895329845000000000000)
      linear := (-2602373915068527429941746761791577000000000000)
      constant := (88624076860839192930725804417746714305191385243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree126.table
  base := (34253575685938674986361281060964186364989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (2184050)
      previous := (1092025)
      next := (1092025)
      square := (19771753933449148222661895329845000000000000)
      linear := (-2605211965872371805284712584087727000000000000)
      constant := (88810951952241627563086513290347325249218169018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139610523238784997727/25000000000000000000)
  centralHi := (558442092955139990909/100000000000000000000)
  directionLo := (560671411571510530123/100000000000000000000)
  directionHi := (140167852892877632531/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree127.table
  base := (140045978184846695376404086227108076556717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 192633210000000000000000000000000000000000000000
      center := (1926332100)
      previous := (963166050)
      next := (963166050)
      square := (17438686969302148732387791680923290000000000000)
      linear := (-2313503294658067474284157952916728544000000000000)
      constant := (79427964035812403497270215645364368225904614277157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree127.table
  base := (7002298909205578166713368737038789397283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-231602632182268512396405456893800589400000000000)
      constant := (7959541398490198346425111641003866178022517913686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560671411571510530123/100000000000000000000)
  centralHi := (140167852892877632531/25000000000000000000)
  directionLo := (28144595054959624063/5000000000000000000)
  directionHi := (562891901099192481261/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree128.table
  base := (35777285873737754376262107930055960849059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 96316605000000000000000000000000000000000000000
      center := (963166050)
      previous := (481583025)
      next := (481583025)
      square := (8719343484651074366193895840461645000000000000)
      linear := (-1165856398112846877679847630966643087000000000000)
      constant := (40349803036733182476206740035654881059597712129878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree128.table
  base := (3577728587358155264736438963855878385329/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19263321000000000000000000000000000000000000000
      center := (192633210)
      previous := (96316605)
      next := (96316605)
      square := (1743868696930214873238779168092329000000000000)
      linear := (-233425568974593831566699263871063657400000000000)
      constant := (8086970289682080463311496611466555247494216870436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell110.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28144595054959624063/5000000000000000000)
  centralHi := (562891901099192481261/100000000000000000000)
  directionLo := (282551832807954029119/50000000000000000000)
  directionHi := (565103665615908058239/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree129.table
  base := (146203798674878276125417926741589424401317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (214036900)
      previous := (107018450)
      next := (107018450)
      square := (1937631885478016525820865742324810000000000000)
      linear := (-261102477532591115159470285661093756000000000000)
      constant := (9109040211580111891718089750357479506216422465973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2294
  qDenominator := 4389
  table := BinomialMassData.Q2294_4389.Degree129.table
  base := (36550949668586817418854273600696373074783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10701845000000000000000000000000000000000000000
      center := (107018450)
      previous := (53509225)
      next := (53509225)
      square := (968815942739008262910432871162405000000000000)
      linear := (-130693614314955083742773928249070403000000000000)
      constant := (4564118130979588301178983052088770212683400429854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2294_4389.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell110.Kernel129
