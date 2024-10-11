#ifndef __ROUTESYNC__
#define __ROUTESYNC__

#include "dbconnector.h"
#include "producerstatetable.h"
#include "netmsg.h"
#include "warmRestartHelper.h"
#include <string.h>
#include <bits/stdc++.h>

using namespace std;

/* Parse the Raw netlink msg */
extern void netlink_parse_rtattr(struct rtattr **tb, int max, struct rtattr *rta,
                                                int len);

namespace swss {

class RouteSync : public NetMsg
{
public:
    enum { MAX_ADDR_SIZE = 64 };

    RouteSync(RedisPipeline *pipeline);

    virtual void onMsg(int nlmsg_type, struct nl_object *obj);

    virtual void onMsgRaw(struct nlmsghdr *obj);
    WarmStartHelper  m_warmStartHelper;

private:
    /* regular route table */
    ProducerStateTable  m_routeTable;
    /* label route table */
    ProducerStateTable  m_label_routeTable;
    /* vnet route table */
    ProducerStateTable  m_vnet_routeTable;
    /* vnet vxlan tunnel table */  
    ProducerStateTable  m_vnet_tunnelTable;
    /* srv6 local sid table */
    ProducerStateTable m_srv6LocalSidTable;
    /* srv6 sid list table */
    ProducerStateTable m_srv6SidListTable;
    struct nl_cache    *m_link_cache;
    struct nl_sock     *m_nl_sock;

    /* Handle regular route (include VRF route) */
    void onRouteMsg(int nlmsg_type, struct nl_object *obj, char *vrf);

    /* Handle label route */
    void onLabelRouteMsg(int nlmsg_type, struct nl_object *obj);

    void parseEncap(struct rtattr *tb, uint32_t &encap_value, string &rmac);

    void parseEncapSrv6SteerRoute(struct rtattr *tb, string &vpn_sid, string &src_addr);

    void parseEncapSrv6LocalSid(struct rtattr *tb, string &block_len,
                                string &node_len, string &func_len,
                                string &arg_len, string &action, string &vrf,
                                string &adj);

    void parseEncapSrv6LocalSidFormat(struct rtattr *tb, string &block_len,
                                      string &node_len, string &func_len,
                                      string &arg_len);

    void parseRtAttrNested(struct rtattr **tb, int max,
                 struct rtattr *rta);

    char *prefixMac2Str(char *mac, char *buf, int size);


    /* Handle prefix route */
    void onEvpnRouteMsg(struct nlmsghdr *h, int len);

    /* Handle routes containing an SRv6 nexthop */
    void onSrv6SteerRouteMsg(struct nlmsghdr *h, int len);

    /* Handle routes containing an SRv6 Local SID nexthop */
    void onSrv6LocalSidMsg(struct nlmsghdr *h, int len);

    /* Handle vnet route */
    void onVnetRouteMsg(int nlmsg_type, struct nl_object *obj, string vnet);

    /* Get interface name based on interface index */
    bool getIfName(int if_index, char *if_name, size_t name_len);

    void getEvpnNextHopSep(string& nexthops, string& vni_list,  
                       string& mac_list, string& intf_list);

    void getEvpnNextHopGwIf(char *gwaddr, int vni_value,
                          string& nexthops, string& vni_list,
                          string& mac_list, string& intf_list,
                          string rmac, string vlan_id);

    bool getEvpnNextHop(struct nlmsghdr *h, int received_bytes, struct rtattr *tb[],
                        string& nexthops, string& vni_list, string& mac_list,
                        string& intf_list);

    bool getSrv6SteerRouteNextHop(struct nlmsghdr *h, int received_bytes,
                        struct rtattr *tb[], vector<string> &vpn_sids,
                        vector<string> &src_addrs);

    bool getSrv6LocalSidNextHop(struct nlmsghdr *h, int received_bytes,
                                struct rtattr *tb[], string &block_len,
                                string &node_len, string &func_len,
                                string &arg_len, string &act, string &vrf,
                                string &adj);

    /* Get next hop list */
    void getNextHopList(struct rtnl_route *route_obj, string& gw_list,
                        string& mpls_list, string& intf_list);

    /* Get next hop gateway IP addresses */
    string getNextHopGw(struct rtnl_route *route_obj);

    /* Get next hop interfaces */
    string getNextHopIf(struct rtnl_route *route_obj);

    /* Get next hop weights*/
    string getNextHopWt(struct rtnl_route *route_obj);

    /* Get encap type */
    uint16_t getEncapType(struct nlmsghdr *h);

    const char *localSidAction2Str(uint32_t action);
};

}

#endif
