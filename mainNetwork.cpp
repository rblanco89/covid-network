#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include "ranNumbers.h"

/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- FUNCTIONS =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

void genWSnet(int *edge, int *nodeDegree, int nEdges,
		int nNodes, int K, float betaWS, Ran ranUni)
{
	int ii, jj, kk, ee, auxInt, accept;

	// Conect each node with its neighboring nodes
	for (ii=0; ii<nNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= nNodes) jj -= nNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	if (betaWS == 0.0) return;

	// Rewire the edges
	for (ee=0; ee<nEdges; ee++)
	{
		ii = ee/K;
		jj = edge[ee];

		if (betaWS < 1.0)
			if (ranUni.doub() >= betaWS) continue; // Do not rewire

		nodeDegree[jj]--;
		accept = 0;
		while (!accept)
		{
			jj = (int) nNodes*ranUni.doub();
			if (jj == ii) continue; // avoid self-loop

			// Find if the edge already exists
			for (kk=0; kk<K; kk++)
			{
				auxInt = kk + ii*K;
				if (edge[auxInt] == jj) break;
				auxInt = kk + jj*K;
				if (edge[auxInt] == ii) break;
				if (kk == K-1) accept = 1; // Accept the edge
			}
		}

		edge[ee] = jj; // Rewire with the new node
		nodeDegree[jj]++;
	}

	return;
}

//---------------------------------------------------------------------------------//

void genBAnet(int *edge, int *nodeDegree, int nNodes, int K, Ran ranUni)
{
	int ii, jj, kk, auxInt;

	// Complete graph with the 2K+1 first nodes
	int initNodes = 2*K + 1;
	for (ii=0; ii<initNodes; ii++) for (kk=0; kk<K; kk++)
	{
		jj = ii + kk + 1;
		if (jj >= initNodes) jj -= initNodes;

		auxInt = kk + ii*K;
		edge[auxInt] = jj;

		nodeDegree[ii]++;
		nodeDegree[jj]++;
	}

	int *bagIds, lenBagIds;
	lenBagIds = (nNodes - initNodes)*(K+1) + initNodes;
	bagIds = (int*) malloc(lenBagIds*sizeof(int));
	memset(bagIds, -1, lenBagIds*sizeof(int));
	for (ii=0; ii<initNodes; ii++) bagIds[ii] = ii; // Collect the initial nodes in the bag

	// Connect each new node to previous nodes with
	// a probability dependent on their degrees
	int ee, bb, accept, trial;
	int countIds;
	countIds = initNodes;
	bb = initNodes;
	for (ii=initNodes; ii<nNodes; ii++)
	{
		for (kk=0; kk<K; kk++)
		{
			accept = 0;
			while (!accept)
			{
				trial = (int) countIds*ranUni.doub();
				if (trial == countIds) trial--;

				jj = bagIds[trial];
				if (jj == ii) continue;

				if (kk == 0) accept = 1; // Accept the edge

				// Find if the edge already exists
				for (ee=0; ee<kk; ee++)
				{
					auxInt = ee + ii*K;
					if (edge[auxInt] == jj) break;
					if (ee == kk-1) accept = 1; // Accept the edge
				}
			}

			ee = kk + ii*K;
			edge[ee] = jj; // Save the edge
			nodeDegree[ii]++;
			nodeDegree[jj]++;
			bagIds[bb++] = jj; // Collect the index of the node jj
		}

		bagIds[bb++] = ii;
		countIds += K + 1;
	}
	free(bagIds);

	return;
}

//---------------------------------------------------------------------------------//

void printNetwork(FILE *fNodes, FILE *fEdges, short *nodeStatus, int *edge,
		int nNodes, int nEdges, int K)
{
	float *xxNode, *yyNode;
	xxNode = (float*) malloc(nNodes*sizeof(float));
	yyNode = (float*) malloc(nNodes*sizeof(float));

	int ii, jj, ee, aux;
	int halfNodes = nNodes/2;
	float ang;
	ang = 2.0*M_PI/nNodes;
	for (ii=0; ii<nNodes; ii++)
	{
		xxNode[ii] = cos(ii*ang);
		yyNode[ii] = sin(ii*ang);
		fprintf(fNodes, "%f\t%f\t%d\n", xxNode[ii], yyNode[ii], nodeStatus[ii]);
	}

	for (ee=0; ee<nEdges; ee++)
	{
		ii = ee/K;
		jj = edge[ee];
		
		// Lockdown
		aux = abs(ii - jj);
		if (aux > halfNodes) aux = nNodes - aux;
		if (aux > K) aux = 1;
		else aux = 0;

		fprintf(fEdges, "%f\t%f\t%f\t%f\t%d\n", xxNode[ii], yyNode[ii],
				xxNode[jj] - xxNode[ii], yyNode[jj] - yyNode[ii], aux);
	}

	free(xxNode);
	free(yyNode);
}

/*=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- MAIN =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*/

int main()
{
	//===| PARAMETERS |===//
	short err_flag = 0;
	long seed;
	int netModel, aveD, initInfec, ldStart, ldEnd, interval, variant2Intro, maxDays;
	float xNodes, betaWS;
	float probInfec1, probInfec2, probDevInfec;
	char renglon[200];

	// Number of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &xNodes);

	// Network model (0: Watts-Strogatz 1: Barabasi-Albert)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &netModel);

	// Average degree of nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &aveD);

	// Probability of rewired (WS)
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &betaWS);

	// Initial infected nodes
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &initInfec);

	// Start of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldStart);

	// End of lockdown
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &ldEnd);

	// Confinament interval
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &interval);

	// Introduction of the variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &variant2Intro);

	// Probability of developing infection
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probDevInfec);

	// Probability of infecting with variant 1
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec1);

	// Probability of infecting with variant 2
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%f", &probInfec2);

	// Maximum number of days to simulate
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%d", &maxDays);

	// Seed for random number
	if (fgets(renglon, sizeof(renglon), stdin) == NULL) err_flag = 1;
	else sscanf(renglon, "%ld", &seed);

	if (err_flag)
	{
		printf("Parameter file error (.data)\n");
		exit (1);
	}

	// Initialize random numbers
	Ran ranUni(seed);
	// Exposed time = 3d +- 1d
	Gammadev gammaE(9.0,3.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2
	// Infected time = 10d +- 3d
	Gammadev gammaI(100.0/9.0,10.0/9.0,seed); // a = (aveTime/stdTime)^2; b = aveTime/stdTime^2

	//===| GENERATE THE NETWORK |===//
	
	int nNodes = xNodes;
	int *nodeDegree;
	nodeDegree = (int*) malloc(nNodes*sizeof(int));
	memset(nodeDegree, 0, nNodes*sizeof(int));

	int K = aveD/2;
	int nEdges = K*nNodes;
	int *edge;
	edge = (int*) malloc(nEdges*sizeof(int));

	if (netModel == 0) // Wattz-Strogatz network
		genWSnet(edge, nodeDegree, nEdges, nNodes, K, betaWS, ranUni);

	if (netModel == 1) // Barabasi-Albert network
		genBAnet(edge, nodeDegree, nNodes, K, ranUni);

	int ee, ii, jj, kk;
       	int auxInt;
	int maxDegree;
	int halfNodes = nNodes/2;

	maxDegree = 0;
	for (ii=0; ii<nNodes; ii++) if (nodeDegree[ii] > maxDegree) maxDegree = nodeDegree[ii];
	maxDegree++;

	// Lockdown: Print degree of the networks
	int *nodeDegreeLD;
	nodeDegreeLD = (int*) malloc(nNodes*sizeof(int));
	for (ii=0; ii<nNodes; ii++) nodeDegreeLD[ii] = nodeDegree[ii];

	for (ee=0; ee<nEdges; ee++)
	{
		ii = ee/K;
		jj = edge[ee];
	
		auxInt = abs(ii - jj);
		if (auxInt > halfNodes) auxInt = nNodes - auxInt;
		if (auxInt <= nNodes/4) continue;

		nodeDegreeLD[ii]--;
		nodeDegreeLD[jj]--;
	}

	int *degree, *degreeLD;
	degree = (int*) malloc(maxDegree*sizeof(int));
	memset(degree, 0, maxDegree*sizeof(int));
	degreeLD = (int*) malloc(maxDegree*sizeof(int));
	memset(degreeLD, 0, maxDegree*sizeof(int));

	for (ii=0; ii<nNodes; ii++)
	{
		degree[nodeDegree[ii]]++;
		degreeLD[nodeDegreeLD[ii]]++;
	}

	FILE *fDegree;
	fDegree = fopen("netDegree.dat", "w");
	fprintf(fDegree, "#Contacts\tFreq\tFreqLD\n");

	for (ee=0; ee<maxDegree; ee++)
		fprintf(fDegree, "%d\t%d\t%d\n", ee, degree[ee], degreeLD[ee]);

	fclose(fDegree);

	free(degree);
	free(degreeLD);
	free(nodeDegree);
	free(nodeDegreeLD);

	//===| SIMULATION |===//
	
	FILE *fNetStatus;
	fNetStatus = fopen("netStatus.dat", "w");
	fprintf(fNetStatus, "#Day\tS\tE\tI\tR\tE2\tI2\tR2\n");

	FILE *fNewCases;
	fNewCases = fopen("newCases.dat", "w");
	fprintf(fNewCases, "#Day\tE\tI\tR\tE2\tI2\tR2\tLock\n");

	// Status (SEIR: Susceptible, Exposed, Infected, Removed)
	// 0:S, 1:E, 2:I, 3:R, -1:E2, -2:I2, -3:R2, 4:D, -4:D2
	short *nodeStatus, *nodeInfec;	

	nodeStatus = (short*) malloc(nNodes*sizeof(short));
	memset(nodeStatus, 0, nNodes*sizeof(short)); // All nodes are susceptibles
	nodeInfec = (short*) malloc(nNodes*sizeof(short));
	memset(nodeInfec, 0, nNodes*sizeof(short));

	int nn;
	int *expTimeNode, *infecTimeNode;

	expTimeNode = (int*) malloc(nNodes*sizeof(int));
	for (nn=0; nn<nNodes; nn++) expTimeNode[nn] = gammaE.dev();
	infecTimeNode = (int*) malloc(nNodes*sizeof(int));
	for (nn=0; nn<nNodes; nn++) infecTimeNode[nn] = gammaI.dev();

	int nContagious;
	int nSuscep, nExpo, nInfec, nRem;
	int nExpo2, nInfec2, nRem2;
	int newE, newI, newR, newE2, newI2, newR2, oldI, daysNewI;
	short iiStatus, jjStatus;

	nSuscep = nNodes;
	nExpo = 0;
	nInfec = 0;
	nRem = 0;
	nExpo2 = 0;
	nInfec2 = 0;
	nRem2 = 0;

	newE = 0;
	newI = 0;
	newR = 0;
	newE2 = 0;
	newI2 = 0;
	newR2 = 0;
	oldI = 0;

	// Choosing random node for Infected status
	for (nn=0; nn<initInfec; nn++)
	{
		auxInt = (int) nNodes*ranUni.doub();
		while (nodeStatus[auxInt] != 0) auxInt = (int) nNodes*ranUni.doub();
		nodeStatus[auxInt] = 2; // Infected
		nSuscep--;
		nInfec++;
		newI++;
	}

	short flagLockdown, flagVariant2, switchLD, count;
	int time, timeLD;

	flagVariant2 = 0;
	flagLockdown = 0;
	switchLD = 0;
	count = 0;
	time = 0;
	timeLD = 0;

//	FILE *fNodes, *fEdges;
//	fNodes = fopen("nodesArray.dat", "w");
//	fprintf(fNodes, "#X\tY\tStatus\n");
//	fEdges = fopen("edgesVec.dat", "w");
//	fprintf(fEdges, "#X1\tY1\tX2\tY2\tLockdown\n");

	while (1)
	{

		nContagious = nExpo + nInfec + nExpo2 + nInfec2;

		// Print the network status
		fprintf(fNetStatus, "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
				time, nSuscep, nExpo, nInfec, nRem, nExpo2, nInfec2, nRem2);
		
		// Print new cases
		fprintf(fNewCases, "%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
				time, newE, newI, newR, newE2, newI2, newR2, switchLD);

		time++;

		if (flagLockdown == 0)
		{
			if (newI + newI2 > oldI) daysNewI++;
			else daysNewI = 0;
			oldI = newI + newI2;
			if (daysNewI > ldStart)
			{
				flagLockdown = 1; // Activate lockdown once
				switchLD = 1;
			}
		}

		if (flagLockdown == 1)
		{
			if (interval > 0)
			{
				count++;
				if (count > interval)
				{
					count = 0;
					if (switchLD) switchLD = 0;
					else switchLD = 1;
				}
			}

			timeLD++;
			if (timeLD > ldEnd)
			{
				flagLockdown = 2;
				switchLD = 0;
			}
		}

		newE = 0;
		newI = 0;
		newR = 0;
		newE2 = 0;
		newI2 = 0;
		newR2 = 0;

		if (nContagious == 0)
		{
			if (flagVariant2 == 1) break;
			if (time < variant2Intro) continue;
		}

		if (time > maxDays) break;
		
		// Find a Susceptible (0) node and infects it with variant 2
		if (time == variant2Intro)
		{
			flagVariant2 = 1;
			for (nn=0; nn<initInfec; nn++)
			{
				auxInt = (int) nNodes*ranUni.doub();
				while (nodeStatus[auxInt] != 0) auxInt = (int) nNodes*ranUni.doub();
				nodeStatus[auxInt] = -2; // Infected 2
				nSuscep--;
				nInfec2++;
				newI2++;
			}
		}

		// Identifies the suceptible nodes and determine if they will be infected
		for (ee=0; ee<nEdges; ee++)
		{
			ii = ee/K;
			jj = edge[ee];

			// Lockdown resriction
			if (switchLD)
			{
				auxInt = abs(ii - jj);
				if (auxInt > halfNodes) auxInt = nNodes - auxInt;
				if (auxInt > K) continue;
			}

			iiStatus = nodeStatus[ii];
			jjStatus = nodeStatus[jj];

			if (iiStatus == 0) // Susceptible
			{
				if (jjStatus == 2) if (ranUni.doub() <= probInfec1) nodeInfec[ii] = 1;
				if (jjStatus == -2) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
			}

			if (iiStatus == 3) // Removed 1
			{
				if (jjStatus == -2) if (ranUni.doub() <= probInfec2) nodeInfec[ii] = -1;
			}

			if (jjStatus == 0) // Susceptible
			{
				if (iiStatus == 2) if (ranUni.doub() <= probInfec1) nodeInfec[jj] = 1;
				if (iiStatus == -2) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
			}

			if (jjStatus == 3) // Removed 1
			{
				if (iiStatus == -2) if (ranUni.doub() <= probInfec2) nodeInfec[jj] = -1;
			}
		}

		// Update states
		for (ii=0; ii<nNodes; ii++)
		{
			iiStatus = nodeStatus[ii];

			if (iiStatus == 0) // Suceptible
			{
				if (nodeInfec[ii] == 1)
				{
					nodeStatus[ii] = 1;
					nSuscep--;
					nExpo++;
					newE++;
				}

				if (nodeInfec[ii] == -1)
				{
					nodeStatus[ii] = -1;
					nSuscep--;
					nExpo2++;
					newE2++;
				}
				nodeInfec[ii] = 0;
				continue;
			}

			if (iiStatus == 1) // Exposed 1
			{
				expTimeNode[ii]--;
				if (expTimeNode[ii] > 0) continue;
				if (ranUni.doub() <= probDevInfec)
				{
					nodeStatus[ii] = 2; // Infected
					nExpo--;
					nInfec++;
					newI++;
				}
				else
				{
					nodeStatus[ii] = 3; // Removed
					nExpo--;
					nRem++;
					newR++;
				}
				expTimeNode[ii] = gammaE.dev();
				continue;
			}

			if (iiStatus == -1) // Exposed 2
			{
				expTimeNode[ii]--;
				if (expTimeNode[ii] > 0) continue;
				if (ranUni.doub() <= probDevInfec)
				{
					nodeStatus[ii] = -2; // Infected 2
					nExpo2--;
					nInfec2++;
					newI2++;
				}
				else
				{
					nodeStatus[ii] = -3; // Removed 2
					nExpo2--;
					nRem2++;
					newR2++;
				}
				continue;
			}

			if (iiStatus == 2) // Infected 1
			{
				infecTimeNode[ii]--;
				if (infecTimeNode[ii] > 0) continue;
				nodeStatus[ii] = 3; // Removed
				nInfec--;
				nRem++;
				newR++;
				infecTimeNode[ii] = gammaI.dev();
				continue;
			}

			if (iiStatus == -2) // Infected 2
			{
				infecTimeNode[ii]--;
				if (infecTimeNode[ii] > 0) continue;
				nodeStatus[ii] = -3; // Removed 2
				nInfec2--;
				nRem2++;
				newR2++;
				continue;
			}

			if (iiStatus == 3) // Removed 1
			{
				if (nodeInfec[ii] == -1)
				{
					nodeStatus[ii] = -1;
					nRem--;
					nExpo2++;
					newE2++;
				}
				nodeInfec[ii] = 0;
				continue;
			}

		}
		//if (time == 5) printNetwork(fNodes, fEdges, nodeStatus, edge, nNodes, nEdges, K);
	}

	fclose(fNetStatus);
	fclose(fNewCases);

//	FILE *fNodes, *fEdges;
//	fNodes = fopen("nodesArray.dat", "w");
//	fprintf(fNodes, "#X\tY\tStatus\n");
//	fEdges = fopen("edgesVec.dat", "w");
//	fprintf(fEdges, "#X1\tY1\tX2\tY2\tLockdown\n");
//	printNetwork(fNodes, fEdges, nodeStatus, edge, nNodes, nEdges, K);
//	fclose(fNodes);
//	fclose(fEdges);

	free(nodeStatus);
	free(nodeInfec);
	free(expTimeNode);
	free(infecTimeNode);
	free(edge);

	exit (0);
}
