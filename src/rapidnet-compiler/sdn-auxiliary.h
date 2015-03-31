/*
 * auxiliary.h
 *
 *  Created on: Mar 2, 2015
 *      Author: cchen
 */

#ifndef SDN_AUXILIARY_H_
#define SDN_AUXILIARY_H_

#include <vector>

using namespace std;

class UnionFindSet
{
public:
	UnionFindSet();

	UnionFindSet(int);

	int Root(int);

	bool Find(int, int);

	void Union(int, int);

private:
	vector<int> elements;
	vector<int> treeSize;
};




#endif /* SDN_AUXILIARY_H_ */
