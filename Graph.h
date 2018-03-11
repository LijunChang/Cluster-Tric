#ifndef _GRAPH_H_
#define _GRAPH_H_

#include "Utility.h"

using namespace std;

class Graph {
private:
	string dir; //input graph directory
	ui n, m; //number of nodes and edges of the graph

	ui *pstart; //offset of neighbors of nodes
	int *edges; //adjacent ids of edges

public:
	Graph(const char *_dir) ;
	~Graph() ;

	void read_graph() ;
	void scan(const char *eps_s, const char *mu_s, int out) ;

private:
	ui binary_search(const int *array, ui e, int val) ;
		//return the first pos, s.t. array[pos] >= val (may return e)

	void get_eps(const char *eps_s, int &eps_a, int &eps_b) ;
		//used for scan to parse the input
	void output(int *similar_degree, int *id, int *pa, vector<pair<int,int> > &noncore_cluster, const char *eps_s, const char *mu) ;

	void my_union(int *pa, int *rank, int u, int v) ;
	int find_root(int *pa, int u) ;
};

#endif
