#include "ortools_extend_sat.h"
#include "bct_entry.hpp"
#include "absl/container/flat_hash_map.h"

#include <iostream>
#include <vector>
#include <array>
#include <tuple>
#include <utility>
#include <cstdint>

using std::cout;
using std::endl;

using namespace operations_research;
using namespace operations_research::sat;

static std::vector< BoolVec > intermediate;
static std::vector< BoolVar > interBits;

template<int branchSize>
constexpr int getAlpha() { return branchSize == 16 ? 7 : 8; }

template<int branchSize>
constexpr int getBeta() { return branchSize == 16 ? 2 : 3; }

static void BVRor(CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;

    for (int i = rn; i < len; ++i) {
        model.AddEquality(output[i - rn], bv0[i]);
    }
    for (int i = 0; i < rn; ++i) {
        model.AddEquality(output[i + (len - rn)], bv0[i]);
    }

    return;
} 

static void BVRol(CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;
    BVRor(model, output, bv0, len - rn);

    return;
} 

template<int branchSize>
static void printm(const std::vector<int> &state)
{
    for (int i = 0; i < 2; ++i) {
        cout << "0b";
        for (int j = 0; j < branchSize; ++j)
            cout << state[i * branchSize + branchSize - 1 - j];
        cout << " | ";
    }
    cout << endl;
    return;
}

template<int branchSize>
static void addAddition_SAT_MILP(CpModelBuilder &model, BoolVec &a, BoolVec &b, BoolVec &output, IntVar &prob)
{
    const std::vector<std::array<int, 8>> eqs{
        {  0,  1, -1,  0,  0,  0,  1,  0 },
        {  1, -1,  0,  0,  0,  0,  1,  0 },
        { -1,  0,  1,  0,  0,  0,  1,  0 },
        { -1, -1, -1,  0,  0,  0, -1, -3 },
        {  1,  1,  1,  0,  0,  0, -1,  0 },
        {  0, -1,  0,  1,  1,  1,  1,  0 },
        {  0,  1,  0,  1, -1,  1,  1,  0 },
        {  0,  1,  0, -1,  1,  1,  1,  0 },
        {  1,  0,  0,  1,  1, -1,  1,  0 },
        {  0,  0,  1, -1, -1, -1,  1, -2 },
        {  0, -1,  0,  1, -1, -1,  1, -2 },
        {  0, -1,  0, -1,  1, -1,  1, -2 },
        {  0, -1,  0, -1, -1,  1,  1, -2 }
    };

    std::vector<std::vector<int64_t>> table2;
    for (int i = 0b000; i <= 0b111; ++i) {
        const int a = (i >> 0) & 1;
        const int b = (i >> 1) & 1;
        const int c = (i >> 2) & 1;
        const int d = a ^ b ^ c;
        table2.push_back({ a, b, c, d, 1 });
    }
    for (int i = 0b0000; i <= 0b1111; ++i) {
        const int a = (i >> 0) & 1;
        const int b = (i >> 1) & 1;
        const int c = (i >> 2) & 1;
        const int d = (i >> 3) & 1;
        table2.push_back({ a, b, c, d, 0 });
    }

    std::vector<BoolVar> equals;

    model.AddBoolXor({ a[0], b[0], output[0], model.TrueVar() });
    for (int i = 0; i < branchSize - 1; ++i) {
        const int eqsSize = eqs.size();
        auto isEqual = model.NewBoolVar();

        for (int j = 0; j < eqsSize; ++j) {
            model.AddGreaterOrEqual(LinearExpr::BooleanScalProd({ a[i],      b[i],      output[i], a[i + 1],  b[i + 1],  output[i + 1], isEqual.Not() },
                                                                { eqs[j][0], eqs[j][1], eqs[j][2], eqs[j][3], eqs[j][4], eqs[j][5],     eqs[j][6] }),
                                    eqs[j][7]);
        }

        auto literal1 = model.NewBoolVar();
        auto literal2 = model.NewBoolVar();
        //model.AddBoolAnd({ a[i - 1], b[i - 1], output[i - 1] }).OnlyEnforceIf(literal1);
        //model.AddBoolOr({ Not(a[i - 1]), Not(b[i - 1]), Not(output[i - 1]) }).OnlyEnforceIf(Not(literal1));
        //model.AddBoolAnd({ Not(a[i - 1]), Not(b[i - 1]), Not(output[i - 1]) }).OnlyEnforceIf(literal2);
        //model.AddBoolOr({ a[i - 1], b[i - 1], output[i - 1] }).OnlyEnforceIf(Not(literal2));
        //model.AddBoolOr({ literal1, literal2 }).OnlyEnforceIf(isEqual);
        //model.AddBoolAnd({ Not(literal1), Not(literal2) }).OnlyEnforceIf(Not(isEqual));

        model.AddGreaterOrEqual(isEqual, literal1);
        model.AddGreaterOrEqual(isEqual, literal2);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal1, literal2 }), isEqual);

        model.AddGreaterOrEqual(a[i], literal1);
        model.AddGreaterOrEqual(b[i], literal1);
        model.AddGreaterOrEqual(output[i], literal1);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal1, model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ a[i], b[i], output[i] }));

        model.AddGreaterOrEqual(a[i].Not(), literal2);
        model.AddGreaterOrEqual(b[i].Not(), literal2);
        model.AddGreaterOrEqual(output[i].Not(), literal2);
        model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literal2, a[i], b[i], output[i] }), model.TrueVar());

        std::vector<BoolVar> tmp1 = { a[i + 1], b[i + 1], output[i + 1], a[i] };
        std::vector<BoolVar> tmp2 = { a[i + 1], b[i + 1], output[i + 1], b[i] };
        std::vector<BoolVar> tmp3 = { a[i + 1], b[i + 1], output[i + 1], output[i] };
        BVAssignIf(model, tmp1, table2, isEqual);
        BVAssignIf(model, tmp2, table2, isEqual);
        BVAssignIf(model, tmp3, table2, isEqual);

        equals.push_back(isEqual);
    }

    model.AddEquality(prob, LinearExpr::BooleanSum(equals));
    return;
}

template<int branchSize>
static void onlyLargeSwitch_BCT_new(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, const int halfNum = 1)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 1, 1, 0, 0, 1},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 1, 0, 0, 1, 1},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 1, 1},
  {0, 0, 1, 1, 1, 0, 1, 0, 1},
  {1, 0, 1, 1, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 1, 1, 0, 0, 1},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 1, 0, 1},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 1, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 1, 0, 1},
  {0, 1, 1, 1, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 1, 1}},
 {{0, 0, 0, 0, 1, 0, 1, 0, 1},
  {1, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 1, 0, 1},
  {1, 1, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 1, 0, 1},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 1, 1, 0, 1},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 1, 0, 0},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 1, 1, 1}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 1, 1},
  {0, 1, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 1, 1},
  {0, 0, 1, 0, 1, 0, 0, 1, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 1, 1},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    //{
    //    {{0, 0, 0, 0, 1, 0, 0, 0, 1},
    //     {1, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 0, 1, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 0, 1, 0, 0, 1, 1},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 0, 0, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 1, 0, 0, 1, 1},
    //     {0, 0, 1, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 1, 1, 0, 0, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 0, 0, 0}},
    //    {{0, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 0, 0, 0, 1, 1, 0, 0, 1},
    //     {0, 1, 0, 0, 1, 1, 0, 0, 1},
    //     {1, 1, 0, 0, 0, 1, 0, 0, 1},
    //     {0, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 1, 1, 0, 1},
    //     {1, 1, 1, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 0, 1, 0, 1, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 1, 0, 0, 0, 0, 0},
    //     {1, 0, 1, 1, 0, 1, 1, 0, 1},
    //     {0, 1, 1, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 1, 0, 1, 0, 1, 1}},
    //    {{0, 0, 0, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 0, 0, 1, 1, 0, 1},
    //     {1, 1, 0, 0, 0, 0, 0, 0, 0},
    //     {0, 0, 1, 0, 1, 0, 1, 0, 1},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 1, 1, 0, 1},
    //     {0, 0, 0, 1, 1, 0, 1, 0, 1},
    //     {1, 0, 0, 1, 0, 1, 1, 0, 1},
    //     {0, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 0, 1, 1, 0, 0, 1, 0, 1},
    //     {1, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {0, 1, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 1, 1, 1}},
    //    {{0, 0, 0, 0, 0, 0, 0, 0, 0},
    //     {1, 0, 0, 0, 1, 0, 0, 1, 1},
    //     {0, 1, 0, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 0, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 0, 1, 0, 0, 1, 1},
    //     {1, 0, 1, 0, 0, 0, 0, 0, 0},
    //     {0, 1, 1, 0, 0, 0, 0, 0, 0},
    //     {1, 1, 1, 0, 0, 1, 0, 1, 1},
    //     {0, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {1, 0, 0, 1, 0, 0, 0, 0, 0},
    //     {0, 1, 0, 1, 1, 0, 0, 1, 1},
    //     {1, 1, 0, 1, 0, 1, 0, 1, 1},
    //     {0, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 0, 1, 1, 0, 0, 1, 1, 1},
    //     {0, 1, 1, 1, 0, 0, 1, 1, 1},
    //     {1, 1, 1, 1, 0, 0, 0, 1, 1}}
    //};

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    std::array< std::array<BoolVar, 4>, branchSize > can0;
    std::array< BoolVar, branchSize > isHalf;

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
            can0[i][j] = model.NewBoolVar();
        }
    for (int i = 0; i < branchSize; ++i)
        isHalf[i] = model.NewBoolVar();
    model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(can0[0][0], model.FalseVar());
    model.AddEquality(can0[0][1], model.TrueVar());
    model.AddEquality(can0[0][2], model.TrueVar());
    model.AddEquality(can0[0][3], model.TrueVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);

            std::array<BoolVar, 4> literals;
            for (int li = 0; li < 4; ++li) literals[li] = model.NewBoolVar();
            for (int r = 0; r < 4; ++r) {
                model.AddBoolAnd({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }).OnlyEnforceIf(literals[r]);
                model.AddBoolOr({ Not(dp[i][cn]), Not(matrix[r * 4 + cn]), Not(can0[i + 1][r]) }).OnlyEnforceIf(Not(literals[r]));

                // milp
                model.AddGreaterOrEqual(dp[i][cn], literals[r]);
                model.AddGreaterOrEqual(matrix[r * 4 + cn], literals[r]);
                model.AddGreaterOrEqual(can0[i + 1][r], literals[r]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r], model.TrueVar(), model.TrueVar() }), LinearExpr::BooleanSum({ dp[i][cn], matrix[r * 4 + cn], can0[i + 1][r] }));
                // milp
            }
            model.AddLessOrEqual(LinearExpr::BooleanSum(literals), halfSize);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        std::array<BoolVar, 4> ifEnforced;
        for (int j = 0; j < 4; ++j) {
            ifEnforced[j] = model.NewBoolVar();
            model.AddBoolAnd({ isHalf[i], can0[i][j] }).OnlyEnforceIf(ifEnforced[j]);
            model.AddBoolOr({ Not(isHalf[i]), Not(can0[i][j]) }).OnlyEnforceIf(Not(ifEnforced[j]));
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(isHalf[i],  ifEnforced[j]);
            model.AddGreaterOrEqual(can0[i][j], ifEnforced[j]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], model.TrueVar() }), LinearExpr::BooleanSum({ isHalf[i], can0[i][j] }));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ ifEnforced[j], Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }
        /*
        model.AddEquality(matrix[0 * 4 + 0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(matrix[1 * 4 + 1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(matrix[2 * 4 + 2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(matrix[3 * 4 + 3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);

        model.AddEquality(dp[i + 1][0], model.TrueVar()).OnlyEnforceIf(dp[i][0]);
        model.AddEquality(dp[i + 1][1], model.TrueVar()).OnlyEnforceIf(dp[i][1]);
        model.AddEquality(dp[i + 1][2], model.TrueVar()).OnlyEnforceIf(dp[i][2]);
        model.AddEquality(dp[i + 1][3], model.TrueVar()).OnlyEnforceIf(dp[i][3]);
        */

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    return;
}

template<int branchSize, bool fixed = false>
static void onlyLargeSwitch_BCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, const int halfNum = 1)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 1, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 1, 1, 0, 0, 1},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 1, 0, 0, 1, 1},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 1, 1},
  {0, 0, 1, 1, 1, 0, 1, 0, 1},
  {1, 0, 1, 1, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 1, 1, 0, 0, 1},
  {1, 0, 0, 0, 1, 1, 0, 0, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 1},
  {1, 1, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 1, 0, 1},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 1, 1, 0, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 1, 0, 1},
  {0, 1, 1, 1, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 1, 1}},
 {{0, 0, 0, 0, 1, 0, 1, 0, 1},
  {1, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 1, 0, 1},
  {1, 1, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 1, 0, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 1, 0, 1},
  {0, 0, 0, 1, 1, 0, 1, 0, 1},
  {1, 0, 0, 1, 0, 1, 1, 0, 1},
  {0, 1, 0, 1, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 1, 0, 0},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 1, 1, 1}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 1, 1},
  {0, 1, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 1, 1},
  {0, 0, 1, 0, 1, 0, 0, 1, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 1, 1},
  {1, 1, 0, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    //std::array< BoolVar, branchSize > isHalf;
    auto isHalf = NewBoolVec(model, branchSize - 1);
    //intermediate.push_back(isHalf);

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
        }
    //for (int i = 0; i < branchSize; ++i)
    //    isHalf[i] = model.NewBoolVar();
    if constexpr (fixed) {
        auto halfSum = model.NewIntVar(Domain(0, branchSize - 1));
        model.AddLessOrEqual(halfSum, model.NewConstant(halfNum));
        model.AddEquality(LinearExpr::BooleanSum(isHalf), halfSum);
        model.AddDecisionStrategy({ halfSum }, DecisionStrategyProto::CHOOSE_FIRST, DecisionStrategyProto::SELECT_MIN_VALUE);
    } else
        model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced = not(isHalf[i]) or not(can0[i][j])

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]

        */

        auto ifEnforced = model.NewBoolVar();
        model.AddEquality(Not(isHalf[i]), ifEnforced);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        /*
        not(ifEnforced) => Or ( dp[i][j] and not(matrix[j * 4 + j]) )
        */
        auto enforcedLiterals = NewBoolVec(model, 4);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 4 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 4 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3] });

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    return;
}

template<int branchSize, bool fixed = false>
static void onlyLargeSwitch_LBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &nLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0},
         {1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
         {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
         {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
        {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
         {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
         {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0},
         {1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
         {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0},
         {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
         {0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0},
         {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}
    };

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1 },
        { 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0 },
        { 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1 }
    };

    std::array< std::array<BoolVar, 8>, branchSize > dp;
    //std::array< BoolVar, branchSize > isHalf;
    auto isHalf = NewBoolVec(model, branchSize - 1);
    //intermediate.push_back(isHalf);

    /*
    {
        BoolVec tmp;
        for (int i = 0; i < branchSize; ++i) tmp.push_back(isHalf[i]);
        intermediate.push_back(tmp);
    }
    */

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 8; ++j) {
            dp[i][j] = model.NewBoolVar();
        }

    //for (int i = 0; i < 8; ++i) {
    //    BoolVec tmp;
    //    for (int j = 0; j < branchSize; ++j)
    //        tmp.push_back(can0[j][i]);
    //    intermediate.push_back(tmp);
    //}
    
    //for (int i = 0; i < branchSize; ++i) {
    //    isHalf[i] = model.NewBoolVar();
    //}
    if constexpr (fixed) {
        //model.AddEquality(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));
        auto halfSum = model.NewIntVar(Domain(0, branchSize - 1));
        model.AddLessOrEqual(halfSum, model.NewConstant(halfNum));
        model.AddEquality(LinearExpr::BooleanSum(isHalf), halfSum);
        model.AddDecisionStrategy({ halfSum }, DecisionStrategyProto::CHOOSE_FIRST, DecisionStrategyProto::SELECT_MIN_VALUE);
    } else
        model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(dp[0][4], model.FalseVar());
    model.AddEquality(dp[0][5], model.FalseVar());
    model.AddEquality(dp[0][6], model.FalseVar());
    model.AddEquality(dp[0][7], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 64);
        for (int cn = 0; cn < 8; ++cn) {
            auto halfSize0 = model.NewBoolVar();
            auto halfSize1 = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(nLL[i]);
            column.push_back(matrix[0 * 8 + cn]);
            column.push_back(matrix[1 * 8 + cn]);
            column.push_back(matrix[2 * 8 + cn]);
            column.push_back(matrix[3 * 8 + cn]);
            column.push_back(matrix[4 * 8 + cn]);
            column.push_back(matrix[5 * 8 + cn]);
            column.push_back(matrix[6 * 8 + cn]);
            column.push_back(matrix[7 * 8 + cn]);
            column.push_back(halfSize0);
            column.push_back(halfSize1);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3], dp[i + 1][4], dp[i + 1][5], dp[i + 1][6], dp[i + 1][7] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        model.AddEquality(Not(isHalf[i]), ifEnforced);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            //model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), Not(matrix[j * 8 + j]) });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        /*
        not(ifEnforced) => Or ( dp[i][j] and not(matrix[j * 4 + j]) )
        */
        auto enforcedLiterals = NewBoolVec(model, 8);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 8 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 8 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3],
                                      enforcedLiterals[4], enforcedLiterals[5], enforcedLiterals[6], enforcedLiterals[7] });

        auto literals = NewBoolVec(model, 64);
        for (int r = 0; r < 8; ++r) {
            for (int c = 0; c < 8; ++c) {
                model.AddBoolAnd({ matrix[r * 8 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 8 + c]);
                model.AddBoolOr({ Not(matrix[r * 8 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 8 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 8 + c],  literals[r * 8 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 8 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 8 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                              literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7]
                            }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 8 + 0]), Not(literals[r * 8 + 1]), Not(literals[r * 8 + 2]), Not(literals[r * 8 + 3]),
                               Not(literals[r * 8 + 4]), Not(literals[r * 8 + 5]), Not(literals[r * 8 + 6]), Not(literals[r * 8 + 7])
                             }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 8; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 8 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                                                             literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7],
                                                           }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(nL[branchSize - 1]);
    isValid.push_back(nR[branchSize - 1]);
    isValid.push_back(nLL[branchSize - 1]);
    for (int i = 0; i < 8; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 8);
    for (int i = 0; i < 8; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[3 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[3 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3],
                      lastLiterals[4], lastLiterals[5], lastLiterals[6], lastLiterals[7] });

    return;
}

template<int branchSize, bool fixed = false>
static void onlyLargeSwitch_UBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &dLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
       {{0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {0, 0, 1, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 1, 0, 0, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 1, 0, 0, 1},
       {0, 1, 0, 0, 0, 1, 1, 0, 0, 1},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 1, 1, 0, 1},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 1, 1, 0, 0, 1},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 1, 0, 1, 1}},
      {{0, 0, 0, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 1, 0, 1, 0, 1},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 1, 1, 0, 1},
       {0, 0, 0, 1, 0, 1, 0, 1, 0, 1},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 1, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 1, 1, 0, 1},
       {1, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 1, 1, 0, 1},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 1, 0, 0, 0, 0, 0}},
      {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 0, 1, 0, 0, 1, 1},
       {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 0, 1, 0, 0, 1, 1},
       {1, 1, 0, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 1, 1, 0, 0, 0, 0, 0, 0},
       {1, 0, 1, 1, 0, 0, 0, 1, 1, 1},
       {0, 1, 1, 1, 0, 0, 0, 1, 1, 1},
       {1, 1, 1, 1, 0, 0, 0, 0, 0, 0},
       {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 0, 1, 1, 0, 0, 1, 1},
       {1, 0, 1, 0, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 0, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 0, 1, 0, 1, 0, 1, 1},
       {0, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 0, 0, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 0, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 0, 1, 1, 0, 1, 0, 1, 1},
       {0, 0, 1, 1, 1, 0, 0, 1, 1, 1},
       {1, 0, 1, 1, 1, 0, 0, 0, 0, 0},
       {0, 1, 1, 1, 1, 0, 0, 0, 0, 0},
       {1, 1, 1, 1, 1, 0, 0, 0, 1, 0}}};

    const std::vector< std::vector<int64_t> > lastTable{
        { 0, 0, 0, 1, 0, 1, 0 },
        { 1, 0, 0, 0, 1, 0, 1 },
        { 0, 1, 0, 0, 1, 0, 1 },
        { 1, 1, 0, 1, 0, 1, 0 },
        { 0, 0, 1, 0, 1, 0, 1 },
        { 1, 0, 1, 1, 0, 1, 0 },
        { 0, 1, 1, 1, 0, 1, 0 },
        { 1, 1, 1, 0, 1, 0, 1 }
    };

    std::array< std::array<BoolVar, 4>, branchSize > dp;
    auto isHalf = NewBoolVec(model, branchSize - 1);

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 4; ++j) {
            dp[i][j] = model.NewBoolVar();
        }
    if constexpr (fixed) {
        auto halfSum = model.NewIntVar(Domain(0, branchSize - 1));
        model.AddLessOrEqual(halfSum, model.NewConstant(halfNum));
        model.AddEquality(LinearExpr::BooleanSum(isHalf), halfSum);
        model.AddDecisionStrategy({ halfSum }, DecisionStrategyProto::CHOOSE_FIRST, DecisionStrategyProto::SELECT_MIN_VALUE);
    } else
        model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 16);
        for (int cn = 0; cn < 4; ++cn) {
            auto halfSize = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(dLL[i]);
            column.push_back(matrix[0 * 4 + cn]);
            column.push_back(matrix[1 * 4 + cn]);
            column.push_back(matrix[2 * 4 + cn]);
            column.push_back(matrix[3 * 4 + cn]);
            column.push_back(halfSize);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        model.AddEquality(Not(isHalf[i]), ifEnforced);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 4 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        auto enforcedLiterals = NewBoolVec(model, 4);
        for (int j = 0; j < 4; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 4 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 4 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3] });

        auto literals = NewBoolVec(model, 16);
        for (int r = 0; r < 4; ++r) {
            for (int c = 0; c < 4; ++c) {
                model.AddBoolAnd({ matrix[r * 4 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 4 + c]);
                model.AddBoolOr({ Not(matrix[r * 4 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 4 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 4 + c],  literals[r * 4 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 4 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 4 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 4 + 0]), Not(literals[r * 4 + 1]), Not(literals[r * 4 + 2]), Not(literals[r * 4 + 3]) }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 4; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 4 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 4 + 0], literals[r * 4 + 1], literals[r * 4 + 2], literals[r * 4 + 3] }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(dL[branchSize - 1]);
    isValid.push_back(dR[branchSize - 1]);
    isValid.push_back(dLL[branchSize - 1]);
    for (int i = 0; i < 4; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 4);
    for (int i = 0; i < 4; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[3 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[3 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3] });

    return;
}

template<int branchSize, bool fixed = false>
static void onlyLargeSwitch_EBCT_enum(CpModelBuilder &model, BoolVec &dL, BoolVec &dR, BoolVec &nL, BoolVec &nR, BoolVec &dLL, BoolVec &nLL, const int halfNum)
{
    const std::vector< std::vector<std::vector<int64_t>> > table{
        {{0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
 {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1},
  {1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1},
  {0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0},
  {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0},
  {1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1},
  {0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0},
  {1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0},
  {0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0},
  {1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}};

    const std::vector< std::vector<int64_t> > lastTable{
        {0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0},
 {1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0},
 {0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0},
 {1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1},
 {1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0}};

    std::array< std::array<BoolVar, 8>, branchSize > dp;
    //std::array< BoolVar, branchSize > isHalf;
    auto isHalf = NewBoolVec(model, branchSize - 1);

    for (int i = 0; i < branchSize; ++i)
        for (int j = 0; j < 8; ++j) {
            dp[i][j] = model.NewBoolVar();
        }

    if constexpr (fixed) {
        auto halfSum = model.NewIntVar(Domain(0, branchSize - 1));
        model.AddLessOrEqual(halfSum, model.NewConstant(halfNum));
        model.AddEquality(LinearExpr::BooleanSum(isHalf), halfSum);
        model.AddDecisionStrategy({ halfSum }, DecisionStrategyProto::CHOOSE_FIRST, DecisionStrategyProto::SELECT_MIN_VALUE);
    } else
        model.AddLessOrEqual(LinearExpr::BooleanSum(isHalf), model.NewConstant(halfNum));

    model.AddEquality(dp[0][0], model.TrueVar());
    model.AddEquality(dp[0][1], model.FalseVar());
    model.AddEquality(dp[0][2], model.FalseVar());
    model.AddEquality(dp[0][3], model.FalseVar());
    model.AddEquality(dp[0][4], model.FalseVar());
    model.AddEquality(dp[0][5], model.FalseVar());
    model.AddEquality(dp[0][6], model.FalseVar());
    model.AddEquality(dp[0][7], model.FalseVar());
    for (int i = 0; i < branchSize - 1; ++i) {
        auto matrix = NewBoolVec(model, 64);
        for (int cn = 0; cn < 8; ++cn) {
            auto halfSize0 = model.NewBoolVar();
            auto halfSize1 = model.NewBoolVar();
            std::vector<BoolVar> column;
            column.push_back(dL[i]);
            column.push_back(dR[i]);
            column.push_back(nL[i]);
            column.push_back(nR[i]);
            column.push_back(dLL[i]);
            column.push_back(nLL[i]);
            column.push_back(matrix[0 * 8 + cn]);
            column.push_back(matrix[1 * 8 + cn]);
            column.push_back(matrix[2 * 8 + cn]);
            column.push_back(matrix[3 * 8 + cn]);
            column.push_back(matrix[4 * 8 + cn]);
            column.push_back(matrix[5 * 8 + cn]);
            column.push_back(matrix[6 * 8 + cn]);
            column.push_back(matrix[7 * 8 + cn]);
            column.push_back(halfSize0);
            column.push_back(halfSize1);
            BVAssign(model, column, table[cn]);
        }
        model.AddBoolOr({ dp[i + 1][0], dp[i + 1][1], dp[i + 1][2], dp[i + 1][3], dp[i + 1][4], dp[i + 1][5], dp[i + 1][6], dp[i + 1][7] });

        /*
        dp[i][j] == 1  =>  dp[i + 1][j] and matrix[j * 4 + j]

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j] and matrix[j * 4 + j]
        ifEnforced = not(isHalf) or not(can0)

        ifEnforced and dp[i][j] == True  =>  dp[i + 1][j]
        ifEnforced and dp[i][j] == True  =>  matrix[j * 4 + j]
        */

        auto ifEnforced = model.NewBoolVar();
        for (int j = 0; j < 8; ++j) {
            model.AddEquality(Not(isHalf[i]), ifEnforced);
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] });
            model.AddBoolOr({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] });

            //model.AddBoolOr({ ifEnforced[j], Not(dp[i][j]), Not(matrix[j * 8 + j]) });

            // milp
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), matrix[j * 8 + j] }), model.NewConstant(1));
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ Not(ifEnforced), Not(dp[i][j]), dp[i + 1][j] }), model.NewConstant(1));
            // milp
        }

        /*
        not(ifEnforced) => Or ( dp[i][j] and not(matrix[j * 4 + j]) )
        */
        auto enforcedLiterals = NewBoolVec(model, 8);
        for (int j = 0; j < 8; ++j) {
            model.AddBoolAnd({ Not(matrix[j * 8 + j]), dp[i][j] }).OnlyEnforceIf(enforcedLiterals[j]);
            model.AddBoolOr({ matrix[j * 8 + j], Not(dp[i][j]) }).OnlyEnforceIf(Not(enforcedLiterals[j]));
        }
        model.AddBoolOr({ ifEnforced, enforcedLiterals[0], enforcedLiterals[1], enforcedLiterals[2], enforcedLiterals[3],
                                      enforcedLiterals[4], enforcedLiterals[5], enforcedLiterals[6], enforcedLiterals[7] });

        auto literals = NewBoolVec(model, 64);
        for (int r = 0; r < 8; ++r) {
            for (int c = 0; c < 8; ++c) {
                model.AddBoolAnd({ matrix[r * 8 + c], dp[i][c] }).OnlyEnforceIf(literals[r * 8 + c]);
                model.AddBoolOr({ Not(matrix[r * 8 + c]), Not(dp[i][c]) }).OnlyEnforceIf(Not(literals[r * 8 + c]));
                // milp
                model.AddGreaterOrEqual(matrix[r * 8 + c],  literals[r * 8 + c]);
                model.AddGreaterOrEqual(dp[i][c],           literals[r * 8 + c]);
                model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + c], model.TrueVar() }), LinearExpr::BooleanSum({ matrix[r * 8 + c], dp[i][c] }));
                // milp
            }
            model.AddBoolOr({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                              literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7]
                            }).OnlyEnforceIf(dp[i + 1][r]);
            model.AddBoolAnd({ Not(literals[r * 8 + 0]), Not(literals[r * 8 + 1]), Not(literals[r * 8 + 2]), Not(literals[r * 8 + 3]),
                               Not(literals[r * 8 + 4]), Not(literals[r * 8 + 5]), Not(literals[r * 8 + 6]), Not(literals[r * 8 + 7])
                             }).OnlyEnforceIf(Not(dp[i + 1][r]));
            // milp
            for (int li = 0; li < 8; ++li)
                model.AddGreaterOrEqual(dp[i + 1][r], literals[r * 8 + li]);
            model.AddGreaterOrEqual(LinearExpr::BooleanSum({ literals[r * 8 + 0], literals[r * 8 + 1], literals[r * 8 + 2], literals[r * 8 + 3],
                                                             literals[r * 8 + 4], literals[r * 8 + 5], literals[r * 8 + 6], literals[r * 8 + 7],
                                                           }), dp[i + 1][r]);
            // milp
        }
    }

    // last validation
    std::vector<BoolVar> isValid;
    isValid.push_back(dL[branchSize - 1]);
    isValid.push_back(dR[branchSize - 1]);
    isValid.push_back(nL[branchSize - 1]);
    isValid.push_back(nR[branchSize - 1]);
    isValid.push_back(dLL[branchSize - 1]);
    isValid.push_back(nLL[branchSize - 1]);
    for (int i = 0; i < 8; ++i) isValid.push_back(model.NewBoolVar());
    BVAssign(model, isValid, lastTable);

    auto lastLiterals = NewBoolVec(model, 8);
    for (int i = 0; i < 8; ++i) {
        model.AddBoolAnd({ dp[branchSize - 1][i], isValid[6 + i] }).OnlyEnforceIf(lastLiterals[i]);
        model.AddBoolOr({ Not(dp[branchSize - 1][i]), Not(isValid[6 + i]) }).OnlyEnforceIf(Not(lastLiterals[i]));
    }
    model.AddBoolOr({ lastLiterals[0], lastLiterals[1], lastLiterals[2], lastLiterals[3],
                      lastLiterals[4], lastLiterals[5], lastLiterals[6], lastLiterals[7] });

    return;
}

template<int branchSize>
static void addRound(CpModelBuilder &model, std::array<BoolVec, 2> &state, std::array<BoolVec, 2> &output, IntVar &prob)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);
    auto afterAddition = NewBoolVec(model, branchSize);

    BVRor(model, afterAlpha, state[0], alpha);
    addAddition_SAT_MILP<branchSize>(model, afterAlpha, state[1], afterAddition, prob);

    BVRol(model, afterBeta, state[1], beta);
    BVXor(model, afterAddition, afterBeta, output[1]);

    for (int i = 0; i < branchSize; ++i)
        model.AddEquality(afterAddition[i], output[0][i]);

    return;
}

template<int branchSize>
static void addSwitch(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, const int halfNum_BCT)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    {
    intermediate.push_back(afterAlpha);
    intermediate.push_back(delta[1]);
    intermediate.push_back(nabla[0]);
    intermediate.push_back(beforeBeta);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    //onlyLargeSwitch_BCT_new(model, afterAlpha, delta[1], nabla[0], beforeBeta, halfNum_BCT);
    onlyLargeSwitch_BCT_enum<branchSize>(model, afterAlpha, delta[1], nabla[0], beforeBeta, halfNum_BCT);

    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);
    return;
}

template<int branchSize>
static void addSwitch2(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, const int halfNum_UBCT, const int halfNum_LBCT)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha1 = NewBoolVec(model, branchSize);
    auto beforeBeta1 = NewBoolVec(model, branchSize);
    auto afterBeta1 = NewBoolVec(model, branchSize);
    auto afterAlpha2 = NewBoolVec(model, branchSize);
    auto beforeBeta2 = NewBoolVec(model, branchSize);
    auto afterBeta2 = NewBoolVec(model, branchSize);
    auto interDeltaL = NewBoolVec(model, branchSize);
    auto interDeltaR = NewBoolVec(model, branchSize);
    auto interNableL = NewBoolVec(model, branchSize);
    auto tmp = NewBoolVec(model, branchSize);

    {
        intermediate.push_back(afterAlpha1);
        intermediate.push_back(delta[1]);
        intermediate.push_back(interNableL);
        intermediate.push_back(beforeBeta1);
        intermediate.push_back(interDeltaL);
        intermediate.push_back(afterAlpha2);
        intermediate.push_back(interDeltaR);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta2);
        intermediate.push_back(interNableL);
    }

    BVRor(model, afterAlpha1, delta[0], alpha);
    BVRol(model, tmp, delta[1], beta);
    BVXor(model, interDeltaL, tmp, interDeltaR);
    onlyLargeSwitch_UBCT_enum<branchSize>(model, afterAlpha1, delta[1], interNableL, beforeBeta1, interDeltaL, halfNum_UBCT);
    BVRol(model, afterBeta1, beforeBeta1, beta);
    BVXor(model, interNableL, afterBeta1, beforeBeta2);

    BVRor(model, afterAlpha2, interDeltaL, alpha);
    onlyLargeSwitch_LBCT_enum<branchSize>(model, afterAlpha2, interDeltaR, nabla[0], beforeBeta2, interNableL, halfNum_LBCT);
    BVRol(model, afterBeta2, beforeBeta2, beta);
    BVXor(model, nabla[0], afterBeta2, nabla[1]);
    return;
}

template<int branchSize, bool fixed = false>
static void _addSwitchUBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &deltaOut, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(deltaOut[0]);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    onlyLargeSwitch_UBCT_enum<branchSize, fixed>(model, afterAlpha, delta[1], nabla[0], beforeBeta, deltaOut[0], halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link deltaOut[1] to delta[1]
    auto tmp = NewBoolVec(model, branchSize);
    BVRol(model, tmp, delta[1], beta);
    BVXor(model, deltaOut[0], tmp, deltaOut[1]);
    return;
}

template<int branchSize, bool fixed = false>
static void _addSwitchLBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &nablaIn, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    auto tmp1 = NewBoolVec(model, branchSize);
    BVRor(model, tmp1, nablaIn[0], alpha);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(tmp1);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    onlyLargeSwitch_LBCT_enum<branchSize, fixed>(model, afterAlpha, delta[1], nabla[0], beforeBeta, tmp1, halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link nablaIn[1] to nabla[1]
    auto tmp2 = NewBoolVec(model, branchSize);
    BVRol(model, tmp2, nablaIn[1], beta);
    BVXor(model, nabla[0], tmp2, nabla[1]);
    return;
}

template<int branchSize, bool fixed = false>
static void _addSwitchEBCT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, std::array<BoolVec, 2> &deltaOut, std::array<BoolVec, 2> &nablaIn, const int halfNum)
{
    constexpr int alpha = getAlpha<branchSize>();
    constexpr int beta = getBeta<branchSize>();

    auto afterAlpha = NewBoolVec(model, branchSize);
    auto beforeBeta = NewBoolVec(model, branchSize);
    auto afterBeta = NewBoolVec(model, branchSize);

    auto tmp1 = NewBoolVec(model, branchSize);
    BVRor(model, tmp1, nablaIn[0], alpha);

    {
        intermediate.push_back(afterAlpha);
        intermediate.push_back(delta[1]);
        intermediate.push_back(nabla[0]);
        intermediate.push_back(beforeBeta);
        intermediate.push_back(deltaOut[0]);
        intermediate.push_back(tmp1);
    }

    BVRor(model, afterAlpha, delta[0], alpha);
    onlyLargeSwitch_EBCT_enum<branchSize, fixed>(model, afterAlpha, delta[1], nabla[0], beforeBeta, deltaOut[0], tmp1, halfNum);
    BVRol(model, afterBeta, beforeBeta, beta);
    BVXor(model, nabla[0], afterBeta, nabla[1]);

    // link deltaOut[1] to delta[1]
    auto tmp2 = NewBoolVec(model, branchSize);
    BVRol(model, tmp2, delta[1], beta);
    BVXor(model, deltaOut[0], tmp2, deltaOut[1]);

    // link nablaIn[1] to nabla[1]
    auto tmp3 = NewBoolVec(model, branchSize);
    BVRol(model, tmp3, nablaIn[1], beta);
    BVXor(model, nabla[0], tmp3, nabla[1]);
    return;
}

template<int branchSize>
static void addSwitchM(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, const int mNum, const int halfNum)
{
    std::vector< std::array<BoolVec, 2> > EBCTs;

    std::array<BoolVec, 2> initEBCTd = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
    std::array<BoolVec, 2> initEBCTn = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
    EBCTs.push_back(initEBCTd);
    EBCTs.push_back(initEBCTn);
    _addSwitchUBCT<branchSize>(model, delta, initEBCTn, initEBCTd, halfNum);

    for (int i = 0; i < mNum; ++i) {
        std::array<BoolVec, 2> EBCTd = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
        std::array<BoolVec, 2> EBCTn = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
        EBCTs.push_back(EBCTd);
        EBCTs.push_back(EBCTn);
        _addSwitchEBCT<branchSize>(model, EBCTs[2 * i], EBCTn, EBCTd, EBCTs[2 * i + 1], halfNum);
    }

    _addSwitchLBCT<branchSize>(model, EBCTs[2 * mNum], nabla, EBCTs[2 * mNum + 1], halfNum);
    return;
}

template<int branchSize, bool fixed = false>
static void addSwitchT(CpModelBuilder &model, std::array<BoolVec, 2> &delta, std::array<BoolVec, 2> &nabla, const int mNum, const int halfNum)
{
    std::array<BoolVec, 2> initEBCTd = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
    std::array<BoolVec, 2> initEBCTn = { NewBoolVec(model, branchSize), NewBoolVec(model, branchSize) };
    _addSwitchUBCT<branchSize, fixed>(model, delta, initEBCTn, initEBCTd, halfNum);
    _addSwitchLBCT<branchSize, fixed>(model, initEBCTd, nabla, initEBCTn, halfNum);
    return;
}

template<int branchSize, int precision>
void search(const int preRound, const int postRound, const int halfNum_BCT, const std::array<unsigned long long int, 2> inputV, const std::array<unsigned long long int, 2> outputV, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 7));
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitch<branchSize>(cp_model, allState[preRound], switchState, halfNum_BCT);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 7));

        //if (i == 3)
        //    cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 2));
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    if (true) {

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((inputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[0][i][j], tmpc);
        }

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((outputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[preRound + 1 + postRound][i][j], tmpc);
        }

    }

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest - precision));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    std::array<long double, precision> probCnt{{ 0 }};
    Model model;
    int num_solutions = 0;
    long double probSum = 0;
    // switch 1
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        const auto prob = SolutionIntegerValue(r, totalProb);
        const int realProb = (branchSize - 1) * (preRound + postRound) - prob;
        //++probCnt[realProb - probBest];

        unsigned long long int dnlr[4] = { 0, 0, 0, 0 };
        for (int i = 0; i < 4; ++i) {
            //cout << "0b";
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[i][branchSize - 1 - j]);
                //cout << bit;
                dnlr[i] = (dnlr[i] << 1) + (bit&1);
            }
            //cout << " | ";
        }
        //cout << endl;

        num_solutions++;
        //cout << realProb << endl;
        cout << "num_solutions = " << num_solutions << endl;

/*
        cout << dnlr[0] << " " << dnlr[1] << " " << dnlr[2] << " " << dnlr[3] << " " << endl;
        cout << "probs:" << endl;
        for (auto &prob : probs) {
            cout << (branchSize - 1) - SolutionIntegerValue(r, prob) << endl;
        }
        cout << endl;

        for (int i = 0; i < 2; ++i) {
            cout << "0b";
            for (int j = 0; j < branchSize; ++j)
                cout << SolutionIntegerValue(r, allState[preRound + 1][i][branchSize - 1 - j]);
            cout << " | ";
        }
        cout << endl;
*/

        const auto bct_cnt = bct_entry(
            dnlr[0],
            dnlr[1],
            dnlr[2],
            dnlr[3], 32);

        //auto prob1 = log2(bct_cnt);
        //cout << prob1 << endl;

        const unsigned long long int pt = (unsigned long long int)(1) << 63;
        probCnt[realProb - probBest] += (bct_cnt * 1.0 / 2 / pt);

        cout << realProb << endl;
        for (auto v : probCnt)
            cout << v << " ";
        cout << endl;
    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    for (int i = 0; i < precision; ++i)
        probSum += probCnt[i] * 1.0 / (1 << (2 * i));
    cout << "2^{-" << probBest * 2 - log2(probSum) << "}" << endl;

    return;
}

template<int branchSize, int precision>
void search2(const int preRound, const int postRound, const int halfNum_UBCT, const int halfNum_LBCT, const std::array<unsigned long long int, 2> inputV, const std::array<unsigned long long int, 2> outputV, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 7));
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitch2<branchSize>(cp_model, allState[preRound], switchState, halfNum_UBCT, halfNum_LBCT);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 7));

        //if (i == 3)
        //    cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 2));
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    if (true) {

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((inputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[0][i][j], tmpc);
        }

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((outputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[preRound + 1 + postRound][i][j], tmpc);
        }

    }

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest - precision));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    std::array<long double, precision> probCnt{{ 0 }};
    Model model;
    int num_solutions = 0;
    long double probSum = 0;
    // switch 2
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        num_solutions++;
        cout << "-----------------------------" << endl
             << "num_solutions = " << num_solutions << endl;

        const auto prob = SolutionIntegerValue(r, totalProb);
        const int realProb = (branchSize - 1) * (preRound + postRound) - prob;
        //++probCnt[realProb - probBest];

        unsigned long long int dnlr[5];
        for (int i = 0; i < 5; ++i) {
            dnlr[i] = 0;
            //cout << "0b";
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[i][branchSize - 1 - j]);
                //cout << bit;
                dnlr[i] = (dnlr[i] << 1) + (bit&1);
            }
            //cout << " | ";
        }
        //cout << endl;
        const auto ubct_cnt = ubct_entry(
            dnlr[0],
            dnlr[1],
            dnlr[2],
            dnlr[3],
            dnlr[4], 32);
        //cout << log2(ubct_cnt) << " ";

        for (int i = 5; i < 10; ++i) {
            dnlr[i - 5] = 0;
            //cout << "0b";
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[i][branchSize - 1 - j]);
                //cout << bit;
                dnlr[i - 5] = (dnlr[i - 5] << 1) + (bit&1);
            }
            //cout << " | ";
        }
        //cout << endl;
        const auto lbct_cnt = lbct_entry(
            dnlr[0],
            dnlr[1],
            dnlr[2],
            dnlr[3],
            dnlr[4], 32);
        //cout << log2(lbct_cnt) << endl;

        //auto prob1 = log2(bct_cnt);
        //cout << prob1 << endl;

        const unsigned long long int pt = (unsigned long long int)(1) << 63;
        probCnt[realProb - probBest] += (ubct_cnt * 1.0 / 2 / pt) * (lbct_cnt * 1.0 / 2 / pt);

        //cout << realProb << endl;
        for (auto v : probCnt)
            cout << v << " ";
        cout << endl;
    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    for (int i = 0; i < precision; ++i)
        probSum += probCnt[i] * 1.0 / (1 << (2 * i));
    cout << "2^{-" << probBest * 2 - log2(probSum) << "}" << endl;

    return;
}

template<int branchSize, int precision>
void search_no_fix(const int preRound, const int postRound, const int halfNum_BCT, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 6));

        if (i == 4)
            cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 1));
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 2)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitch<branchSize>(cp_model, allState[preRound], switchState, halfNum_BCT);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 6));

        if (i == 3)
            cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 1));
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - branchSize));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    std::array<long double, precision> probCnt{{ 0 }};
    Model model;
    int num_solutions = 0;
    long double probSum = 0;
    //std::unordered_map< unsigned long long int, int > ioCnt;
    absl::flat_hash_map< std::vector<unsigned int>, int > ioCnt;
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        const auto prob = SolutionIntegerValue(r, totalProb);
        const int realProb = (branchSize - 1) * (preRound + postRound) - prob;
        //++probCnt[realProb - probBest];

        unsigned long long int dnlr[4] = { 0, 0, 0, 0 };
        for (int i = 0; i < 4; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[i][branchSize - 1 - j]);
                dnlr[i] = (dnlr[i] << 1) + (bit&1);
            }
        }

        unsigned int ind[2];
        unsigned int outd[2];
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, inputDiff[i][branchSize - 1 - j]);
                ind[i] = (ind[i] << 1) + (bit & 1);
            }
        }
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, allState[preRound + 1 + postRound][i][branchSize - 1 - j]);
                outd[i] = (outd[i] << 1) + (bit & 1);
            }
        }

        std::vector<unsigned int> vtmp{{ ind[0], ind[1], outd[0], outd[1] }};
        //const unsigned long long int ip = (ind[0] << 32) + outd[1];
        auto isExist = ioCnt.find(vtmp);
        if (isExist == ioCnt.end())
            ioCnt.insert(std::make_pair(vtmp, 1));
        else
            ++ioCnt[vtmp];

        num_solutions++;
        //cout << realProb << endl;
        cout << "num_solutions = " << num_solutions << endl;

        const auto bct_cnt = bct_entry(
            dnlr[0],
            dnlr[1],
            dnlr[2],
            dnlr[3], 32);

        auto prob1 = log2(bct_cnt);
        cout << realProb << " " << prob1 << endl;

        //const unsigned long long int pt = (unsigned long long int)(1) << 63;
        //probCnt[realProb - probBest] += (bct_cnt * 1.0 / 2 / pt);

        //cout << realProb << endl;
        //for (auto v : probCnt)
        //    cout << v << " ";
        //cout << endl;
    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    for (auto it : ioCnt)
        cout << it.first[0] << " " << it.first[1] << " " << it.first[2] << " " << it.first[3] << " " << " : " << it.second << endl;

    for (int i = 0; i < precision; ++i)
        probSum += probCnt[i] * 1.0 / (1 << i);
    cout << "2^{-" << probBest * 2 - log2(probSum) << "}" << endl;

    return;
}

template<int branchSize, int precision>
void search2_no_fix(const int preRound, const int postRound, const int halfNum_UBCT, const int halfNum_LBCT, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 10));

        if (i == 1) {
            cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitch2<branchSize>(cp_model, allState[preRound], switchState, halfNum_UBCT, halfNum_LBCT);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 10));

        if (i == postRound) {
            cp_model.AddEquality(prob, cp_model.NewConstant((branchSize - 1)));
        }
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest - precision));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    Model model;
    int num_solutions = 0;
    //std::unordered_map< unsigned long long int, int > ioCnt;
    absl::flat_hash_map< std::vector<unsigned int>, int > ioCnt;
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        num_solutions++;
        cout << "-----------------------------" << endl
             << "num_solutions = " << num_solutions << endl;

        unsigned int ind[2] = {};
        unsigned int outd[2] = {};
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, inputDiff[i][branchSize - 1 - j]);
                ind[i] = (ind[i] << 1) + (bit & 1);
            }
        }
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, allState[preRound + 1 + postRound][i][branchSize - 1 - j]);
                outd[i] = (outd[i] << 1) + (bit & 1);
            }
        }

        std::vector<unsigned int> vtmp{{ ind[0], ind[1], outd[0], outd[1] }};
        auto isExist = ioCnt.find(vtmp);
        if (isExist == ioCnt.end())
            ioCnt.insert(std::make_pair(vtmp, 1));
        else
            ++ioCnt[vtmp];
    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    for (auto it : ioCnt)
        cout << it.first[0] << " " << it.first[1] << " " << it.first[2] << " " << it.first[3] << " " << " : " << it.second << endl;

    return;
}

template<int branchSize, int precision, bool fixed = false>
void searchM(const int preRound, const int postRound, const int mNum, const int halfNum, const std::array<uint64_t, 2> inputV, const std::array<uint64_t, 2> outputV, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 9));
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitchM<branchSize>(cp_model, allState[preRound], switchState, mNum, halfNum);
    //addSwitchT<branchSize, fixed>(cp_model, allState[preRound], switchState, mNum, halfNum);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 9));
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    if (true) {

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((inputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[0][i][j], tmpc);
        }

    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j) {
            auto tmpc = ((outputV[i] >> j) & 1) == 0 ? cp_model.FalseVar() : cp_model.TrueVar();
            cp_model.AddEquality(allState[preRound + 1 + postRound][i][j], tmpc);
        }

    }

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest - precision));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    if constexpr (fixed)
        parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    std::array<long double, precision> probCnt{{ 0 }};
    Model model;
    int num_solutions = 0;
    long double probSum = 0;
    // switch 2
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        num_solutions++;
        cout << "-----------------------------" << endl
             << "num_solutions = " << num_solutions << endl;

        const auto prob = SolutionIntegerValue(r, totalProb);
        const int realProb = (branchSize - 1) * (preRound + postRound) - prob;
        //++probCnt[realProb - probBest];

        long double mProb = 1;
        uint64_t dnlr[6];
        // ubct in the head
        for (int i = 0; i < 5; ++i) {
            dnlr[i] = 0;
            //cout << "0b";
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[i][branchSize - 1 - j]);
                //cout << bit;
                dnlr[i] = (dnlr[i] << 1) + (bit&1);
            }
            //cout << " | ";
        }
        //cout << endl;
        if constexpr (branchSize < 64 / 2) {
            const uint64_t pt = (uint64_t)(1) << (2 * branchSize);
            const auto ubct_cnt = ubct_entry(
                dnlr[0],
                dnlr[1],
                dnlr[2],
                dnlr[3],
                dnlr[4], branchSize);
            mProb *= ubct_cnt * 1.0 / pt;
        } else {
            const auto ubct_prob = ubct_entry128(
                dnlr[0],
                dnlr[1],
                dnlr[2],
                dnlr[3],
                dnlr[4], branchSize);
            mProb *= ubct_prob;
        }
        //cout << log2(ubct_cnt) << " ";
        for (int mi = 0; mi < mNum; ++mi) {
            for (int i = 0; i < 6; ++i) {
                dnlr[i] = 0;
                //cout << "0b";
                for (int j = 0; j < branchSize; ++j) {
                    const unsigned int bit = SolutionIntegerValue(r, intermediate[5 + 6 * mi + i][branchSize - 1 - j]);
                    //cout << bit;
                    dnlr[i] = (dnlr[i] << 1) + (bit&1);
                }
                //cout << " | ";
            }
            //cout << endl;
            if constexpr (branchSize < 64 / 2) {
                const uint64_t pt = (uint64_t)(1) << (2 * branchSize);
                const auto ebct_entryv = ebct_entry(dnlr[0], dnlr[1], dnlr[2], dnlr[3], dnlr[4], dnlr[5], branchSize);
                mProb *= ebct_entryv * 1.0 / pt;
                //cout << ebct_entryv << " = 2^{" << log2(ebct_entryv) << "}" << endl;
            } else {
                const auto ebct_prob = ebct_entry128(dnlr[0], dnlr[1], dnlr[2], dnlr[3], dnlr[4], dnlr[5], branchSize);
                //cout << ebct_prob << " = 2^{" << log2(ebct_prob) << "}" << endl;
                mProb *= ebct_prob;
            }
        }
        // lbct in the tail
        for (int i = 0; i < 5; ++i) {
            dnlr[i] = 0;
            //cout << "0b";
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, intermediate[5 + 6 * mNum + i][branchSize - 1 - j]);
                //cout << bit;
                dnlr[i] = (dnlr[i] << 1) + (bit&1);
            }
            //cout << " | ";
        }
        //cout << endl;
        if constexpr (branchSize < 64 / 2) {
            const uint64_t pt = (uint64_t)(1) << (2 * branchSize);
            const auto lbct_cnt = lbct_entry(
                dnlr[0],
                dnlr[1],
                dnlr[2],
                dnlr[3],
                dnlr[4], branchSize);
            mProb *= lbct_cnt * 1.0 / pt;
        } else {
            const auto lbct_prob = lbct_entry128(
                dnlr[0],
                dnlr[1],
                dnlr[2],
                dnlr[3],
                dnlr[4], branchSize);
            mProb *= lbct_prob;
        }

        probCnt[realProb - probBest] += mProb;

        //cout << realProb << endl;
        for (auto v : probCnt)
            cout << v << " ";
        cout << endl;
    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    cout << endl
         << branchSize << " " << precision << " " << preRound << " " << postRound << " " << mNum << " " << halfNum << " " << probBest << " "
         << endl
         << inputV[0] << ", " << inputV[1] << "  "
         << outputV[0] << ", " << outputV[1]
         << endl << endl;

    for (int i = 0; i < precision; ++i) {
        const uint64_t pt = (uint64_t)(1) << (2 * i);
        probSum += probCnt[i] * 1.0 / pt;
    }
    cout << "2^{-" << probBest * 2 - log2(probSum) << "}" << endl;

    return;
}

template<int branchSize, int precision>
void searchM_no_fix(const int preRound, const int postRound, const int mNum, const int halfNum, const int probBest)
{
    CpModelBuilder cp_model;
    std::vector<IntVar> probs;
    std::vector< std::array<BoolVec, 2> > allState;

    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(inputDiff);

    std::vector<BoolVar> inputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            inputBits.push_back(inputDiff[i][j]);
    cp_model.AddBoolOr(inputBits);

    for (int i = 1; i <= preRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 4));

        if (i == 3 || i == 4 || i == 5) {
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 3));
        }
    }

    auto e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    cp_model.AddEquality(e1Prob, LinearExpr::Sum(probs));

    std::array<BoolVec, 2> switchState = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    allState.push_back(switchState);

    addSwitchM<branchSize>(cp_model, allState[preRound], switchState, mNum, halfNum);

    for (int i = 1; i <= postRound; ++i) {
        std::array<BoolVec, 2> state = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
        allState.push_back(state);

        auto prob = cp_model.NewIntVar(Domain(0, branchSize - 1));
        probs.push_back(prob);

        addRound<branchSize>(cp_model, allState[preRound + 1 + i - 1], state, prob);
        cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 6));

        if (i == 3 || i == 4 || i == 5) {
            //cp_model.AddGreaterOrEqual(prob, cp_model.NewConstant((branchSize - 1) - 3));
        }
    }

    std::vector<BoolVar> outputBits;
    for (int i = 0; i < 2; ++i)
        for (int j = 0; j < branchSize; ++j)
            outputBits.push_back(allState[preRound + 1 + postRound][i][j]);
    cp_model.AddBoolOr(outputBits);

    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    cp_model.AddEquality(totalProb, LinearExpr::Sum(probs));

    //cp_model.Maximize(totalProb);
    cp_model.AddLessOrEqual(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest));
    cp_model.AddGreaterThan(totalProb, cp_model.NewConstant((branchSize - 1) * (preRound + postRound) - probBest - precision));

    auto model_built = cp_model.Build();

    SatParameters parameters;
    //parameters.set_search_branching(SatParameters::FIXED_SEARCH);
    //parameters.set_num_search_workers(8);
    //parameters.set_log_search_progress(true);
    parameters.set_enumerate_all_solutions(true);

    Model model;
    int num_solutions = 0;
    absl::flat_hash_map< std::vector<uint64_t>, int > ioCnt;
    model.Add(NewFeasibleSolutionObserver([&](const CpSolverResponse& r) {
        num_solutions++;
        cout << "-----------------------------" << endl
             << "num_solutions = " << num_solutions << endl;

        //const auto prob = SolutionIntegerValue(r, totalProb);
        //const int realProb = (branchSize - 1) * (preRound + postRound) - prob;

        uint64_t ind[2] = {};
        uint64_t outd[2] = {};
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, inputDiff[i][branchSize - 1 - j]);
                ind[i] = (ind[i] << 1) + (bit & 1);
            }
        }
        for (int i = 0; i < 2; ++i) {
            for (int j = 0; j < branchSize; ++j) {
                const unsigned int bit = SolutionIntegerValue(r, allState[preRound + 1 + postRound][i][branchSize - 1 - j]);
                outd[i] = (outd[i] << 1) + (bit & 1);
            }
        }

        std::vector<uint64_t> vtmp{{ ind[0], ind[1], outd[0], outd[1] }};
        auto isExist = ioCnt.find(vtmp);
        if (isExist == ioCnt.end())
            ioCnt.insert(std::make_pair(vtmp, 1));
        else
            ++ioCnt[vtmp];

    }));
    model.Add(NewSatParameters(parameters));

    const auto response = SolveCpModel(model_built, &model);
    cout << "wall time: " << response.wall_time() << endl;

    cout << endl
         << preRound << " "
         << postRound << " "
         << mNum << " "
         << halfNum << " "
         << probBest
         << endl << endl;

    int cntMax = 0;
    int cntMin = 1000000;
    for (auto it : ioCnt) {
        const auto cntTmp = it.second;
        cntMax = cntTmp > cntMax ? cntTmp : cntMax;
        cntMin = cntTmp < cntMin ? cntTmp : cntMin;
    }
    cntMin = (cntMin + cntMax) / 2;
    for (auto it : ioCnt) {
        if (it.second < cntMin) continue;
        cout << it.first[0] << " " << it.first[1] << " " << it.first[2] << " " << it.first[3] << " " << " : " << it.second << endl;
    }

    return;
}


int main()
{
    //searchM_no_fix<32 / 2, 1>(4, 4, 0, 8, 10);

    //searchM<32 / 2, 8>(4, 4, 0, 32,
    //    { 0b0010100000000000, 0b0000000000010000 },
    //    { 0b1000000100000010, 0b1000000100001000 },
    //    10
    //); // 29.1564 (the probability increased because of the increment of the precision)

    //searchM_no_fix<48 / 2, 1>(5, 5, 0, 12, 20);

    //searchM<48 / 2, 6>(5, 5, 0, 24,
    //    { 131202, 1180160 },
    //    { 32928, 2131364 },
    //    20
    //); // 44.1567

    return 0;
}
