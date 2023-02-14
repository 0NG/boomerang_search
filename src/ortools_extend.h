#pragma once

#include <vector>
#include <string>
#include <cassert>

#include "ortools/sat/cp_model.h"
#include "ortools/linear_solver/linear_solver.h"

using namespace operations_research;

using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;

using MPBoolVec = std::vector<MPVariable*>;

BoolVec NewBoolVec(sat::CpModelBuilder &model, const int size = 4)
{
    // bv[0] is the lsb
    BoolVec bv;
    for (int i = 0; i < size; ++i) bv.push_back(model.NewBoolVar());
    return bv;
}

MPBoolVec NewBoolVec(MPSolver &solver, const int size = 4, const std::string name = "error")
{
    if (name == "error") {
        MPBoolVec bv;
        return bv;
    }
    // bv[0] is the lsb
    MPBoolVec bv;
    for (int i = 0; i < size; ++i) bv.push_back(solver.MakeBoolVar(name + std::to_string(i)));
    return bv;
}


IntVec BV2IV(BoolVec &bv)
{
    const int len = bv.size();

    IntVec iv;
    for (int i = 0; i < len; ++i) iv.push_back(sat::IntVar(bv[i]));
    return iv;
}

void BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1, BoolVec &bv2)
{
    /*
     * bv0 ^ bv1 = bv2
     */
    const int len = bv0.size();

    for (int i = 0; i < len; ++i) {
        model.AddBoolXor({bv0[i], bv1[i], bv2[i], model.TrueVar()});
    }

    return;
}

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::IntVar b)
{
    auto iv = BV2IV(bv);
    iv.push_back(b);
    auto table = model.AddAllowedAssignments(iv);

    for (auto &value : values) {
        table.AddTuple(value);
    }

    return;
} 

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::BoolVar b)
{
    BVAssignIf(model, bv, values, sat::IntVar(b));
    return;
} 

void BVAssign(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values)
{
    auto iv = BV2IV(bv);
    auto table = model.AddAllowedAssignments(iv);

    for (auto &value : values) {
        table.AddTuple(value);
    }

    return;
} 

BoolVec BVRor(const BoolVec &bv, const int rotation)
{
    const int len = bv.size();
    const int rn = rotation % len;

    BoolVec output;
    for (int i = rn; i < len; ++i) {
        output.push_back(bv[i]);
    }
    for (int i = 0; i < rn; ++i) {
        output.push_back(bv[i]);
    }
    return output;
} 

MPBoolVec BVRor(const MPBoolVec &bv, const int rotation)
{
    const int len = bv.size();
    const int rn = rotation % len;

    MPBoolVec output;
    for (int i = rn; i < len; ++i) {
        output.push_back(bv[i]);
    }
    for (int i = 0; i < rn; ++i) {
        output.push_back(bv[i]);
    }
    return output;
} 

BoolVec BVRol(BoolVec &bv, const int rotation)
{
    const int len = bv.size();
    const int rn = rotation % len;

    return BVRor(bv, len - rn);
} 

MPBoolVec BVRol(MPBoolVec &bv, const int rotation)
{
    const int len = bv.size();
    const int rn = rotation % len;

    return BVRor(bv, len - rn);
} 

BoolVec BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1)
{
    const int len = bv0.size();
    BoolVec bv2 = NewBoolVec(model, len);

    for (int i = 0; i < len; ++i) {
        model.AddBoolXor({bv0[i], bv1[i], bv2[i], model.TrueVar()});
    }

    return bv2;
}

//
// return b0 ^ b1 with specific name
//
MPVariable *MPBoolXor(MPSolver &model, MPVariable *b0, MPVariable *b1, const std::string name)
{
    auto b2 = model.MakeBoolVar(name);
    auto dummy = model.MakeBoolVar(name + "_dummy");

    auto c0 = model.MakeRowConstraint(0, 0);
    c0->SetCoefficient(b0, 1);
    c0->SetCoefficient(b1, 1);
    c0->SetCoefficient(b2, 1);
    c0->SetCoefficient(dummy, -2);

    return b2;
}

//
// b2 = b0 ^ b1
//
void MPBoolXor(MPSolver &model, MPVariable *b0, MPVariable *b1, MPVariable *b2)
{
    auto dummy = model.MakeBoolVar(b2->name() + "_dummy");

    auto c0 = model.MakeRowConstraint(0, 0);
    c0->SetCoefficient(b0, 1);
    c0->SetCoefficient(b1, 1);
    c0->SetCoefficient(b2, 1);
    c0->SetCoefficient(dummy, -2);

    return;
}

//
// return bv0 ^ bv1 with specific name
//
MPBoolVec BVXor(MPSolver &model, MPBoolVec &bv0, MPBoolVec &bv1, const std::string name)
{
    const int len = bv0.size();
    MPBoolVec bv2 = NewBoolVec(model, len, name);

    for (int i = 0; i < len; ++i) {
        MPBoolXor(model, bv0[i], bv1[i], bv2[i]);
    }

    return bv2;
}

//
// bv2 = bv0 ^ bv1
//
MPBoolVec BVXor(MPSolver &model, MPBoolVec &bv0, MPBoolVec &bv1, MPBoolVec &bv2)
{
    const int len = bv0.size();

    for (int i = 0; i < len; ++i) {
        MPBoolXor(model, bv0[i], bv1[i], bv2[i]);
    }

    return bv2;
}

