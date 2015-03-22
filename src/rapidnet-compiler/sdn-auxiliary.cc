/*
 * auxiliary.cc
 *
 *  Created on: Mar 2, 2015
 *      Author: cchen
 */

#include "sdn-auxiliary.h"

UnionFindSet::UnionFindSet()
{
	elements = vector<int>();
	treeSize = vector<int>();
}

UnionFindSet::UnionFindSet(int size)
{
	elements = vector<int>(size, 0);
	treeSize = vector<int>(size, 1);
	for (int i = 0;i < size;i++)
	{
		elements[i] = i;
	}
}

int
UnionFindSet::Root(int obj)
{
	int curId = obj;
	vector<int> pathMark;

	while (elements[curId] != curId)
	{
		pathMark.push_back(curId);
		curId = elements[curId];
	}

	//Pass compression
	vector<int>::iterator itv;
	for (itv = pathMark.begin();itv != pathMark.end();itv++)
	{
		elements[*itv] = curId;
	}

	return curId;
}

bool
UnionFindSet::Find(int objF, int objS)
{
	return (Root(objF) == Root(objS)?true:false);
}

void
UnionFindSet::Union(int objF, int objS)
{
	int rootF = Root(objF);
	int rootS = Root(objS);

	if (treeSize[rootF] > treeSize[rootS])
	{
		elements[rootS] = rootF;
		treeSize[rootF] = treeSize[rootF] + treeSize[rootS];
	}
	else
	{
		elements[rootF] = rootS;
		treeSize[rootS] = treeSize[rootF] + treeSize[rootS];
	}
}

